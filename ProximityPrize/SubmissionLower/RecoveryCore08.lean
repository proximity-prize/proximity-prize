import ProximityPrize.SubmissionLower.RecoveryCore07
set_option autoImplicit false
set_option linter.all false
set_option Elab.async true
section
namespace ProximityPrize.SubmissionLower
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option autoImplicit false
namespace DBU
open AI AP AN
noncomputable section
def band:Band:=⟨10,49,4336,4362,8672446898194066⟩

private theorem block0:WideCovered band 6422469 9719978:=PRB band Z1.f1742 6422469 9719978 (WB 211735305336 23 0x680b3b97b88899ece5142ab4059d8b0045d2f47269e19a02cee6bea1f5604924d6dc018773e4cdcd81dc8a5e7e00c3b9d886daf7ce432c03005fdcdfc3683747209463802fee7531b164cb8fc962c017f737f8d77ae9c7a449e00bfb9aa26b1ff8e3b1f13005fdcc9b35402471c8deb782fee5ef1a7774b8dc626bc17f72c58d26fd1c6a2abde0bfb9488688db0e331222f05ddc96433ef1a7188773782eee53f19d96db8bc2eabc17772784cdcf29c5a10dde0bbb926c666132e2b0532f05ddc88332ec5371480f9702eee3e2995359b89bfad062b76016001eeed449f6f03173b0060008ce4620f50012b3d802b002bbe10c74060801ec0180015ce882338a) (by decide+kernel)

private theorem block1:WideCovered band 9719979 10642700:=PRB band Z1.f1665 9719979 10642700 (WB 206366596120 14 0x36bbbe9e6a1d20344ca19b5ddf2234f8adaa165b2daeef8b3a70f8b50320a6d6f7bb61335f367d89db5b7bd92897b56f3cc1b1adbde9bb4a96689d5f3ad6def34c24a587ce2ece6b6f79cf92141926d6ffb5b7bca128f027f34b4bfadbde2bf46d74b9958c1d2ceefe5230174cc2b91e967770a914d9ce5d56174b3bae9888e6052ca7cda59dd09c4470ec955248) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6422469 10642700:=(_Q1 band 6422469 9719978 10642700 block0 block1)
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤49)
    (hT0:4336≤T) (hT1:T≤4362) (hnu:6422469≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤8672446898194066:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBU
namespace CZJ
open AI AP AN
noncomputable section








open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CZJ
namespace CYD
open AI AP AN
noncomputable section
def band:Band:=⟨10,51,4181,4310,11453932412571267⟩

private theorem block0:WideCovered band 6684611 9351576:=PRB band Z1.f1743 6684611 9351576 (WB 206366660696 25 0xc2ff6eeaecb2c328eb198c2ff6e794ca01ce8e2db9c2ff6e106c910128da9dac2ff6da0ac817d28d25fbbeff6d1d2c6e3a28ca21cbeff6c9f0c5e8628c1e3dbeff6c058c49c1a8b9a5ebeff6b700c391de8b167fbeef6c734c2963a8a92a0beef6c004c198628a0ec1beef6b948c0d806898ae2beef6b108bfd216890703beef6a91abf0ed6888324baef6a05ebe4bca87ff45baef6956abd3132877b66baef68a3ebc647e86f786baef69176bb2ce28673a7badf69ae0ba817685efc8badf6937cb9fcce856be9badf68a2ab92f6284e80abadf680ccb8b3ce84642b067f4042201e29583e04c059f4044401e1d882d88e041f4045601e0347eb995041f4044601dcfc767ba4) (by decide+kernel)

private theorem block1:WideCovered band 9351577 10060517:=PRB band Z1.f1744 9351577 10060517 (WB 206366661688 16 0xd6df78a3a890f1e9982e5d6df7487888149e987b27d6df6d0f687c990977368dadf586fe8e95a6966baadadf720158d2a179563ecc71f724da6cc9d0945c2ec71f71ccc6c181693d84fc70f713566b3f96935470c70f71a386a94da92d091c70f712ea69e8a4924cb2c70f70c3a6957de91c8d3c70f7054a68c6389144f4c30f6fd1c68129c90c115c30f6f57c677c56903d36c30f6ecc466cc488fb957c2ff6e3ce6622528f3577) (by decide+kernel)

private theorem block2:WideCovered band 10060518 11005170:=PRB band Z1.f1294 10060518 11005170 (WB 206366694424 14 0xe30f67b49547e09a7ecf2e2ff66d8353104ea6e78ce2ff65d6651616ea5dfcedeff64e234fe300a4d810deff63d904e5177a3d052deff63b024cf174a2c894deff62d4d4ba94fa1c0d6daef61ec94a61fea0b918daef6117a496e239fb159daef6110c48240b9ea99bdaef605d5473b869da1dddaef5f8db465ca89c9a1fdaef5ea9b4598319b9261d6df5db81452bb49a8aa3) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6684611 11005170:=(_Q1 band 6684611 9351576 11005170 block0 (_Q1 band 9351577 10060517 11005170 block1 block2))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤51)
    (hT0:4181≤T) (hT1:T≤4310) (hnu:6684611≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤11453932412571267:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYD
namespace DCQ
open AI AP AN
noncomputable section










open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DCQ
namespace DAR
open AI AP AN
noncomputable section










open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DAR
namespace DAY
open AI AP AN
noncomputable section
def band:Band:=⟨10,54,3968,4230,12128527754247205⟩

private theorem block0:WideCovered band 7077824 8824574:=PRB band Z1.f1745 7077824 8824574 (WB 206367809688 21 0xbee8050c702cb67b986a6febee804f0682ca7e79861e87bee804cbf02c8d7b9859610bee8049cdc2c71c89850d99bee804621a2c85399848522bee80408982c8184983fcabbee8037aca2c95089837434bee802761e2cecdb882ebbdbee802a4702c63da7826346b2c8146162a49abc681dacfb2c80e306e7369a36815258b2c813682a9f54b4480c9e1b2c8151526b172e5380416ab2c815e662b0ecb357fb8f3b2c8170146d18a1147f307cb2c80df52a751f1d47e1f8eb2c8062f4dad829c37d0ea006c800053c00421d27bfdb2059800055a0041f317aecc405080003ba0028c5078cae804180003ba0028a80748730) (by decide+kernel)

private theorem block1:WideCovered band 8824575 9383535:=PRB band Z1.f1155 8824575 9383535 (WB 206367741976 16 0xc3081718f30107d8f2e6fc30816d3aafd86f8ea5f8c308167ea2f8c218e1d80c30816702af3cad8d9509c2f816c1baf01df8d0c92c2f8168282ec8728c841bc2f816422ae96228bfba4c2f815fd22e65ef8b732dc2f815abd2e2aed8aeab6bef8155afae03e78a623fbef814f432dc70689d9c8bef8147ce2d879a895151bef8148ee2d60fc88c8dabee8151efad1bf8884063bee814e7a2cef8087b7ecbee8149872cdc79872f75) (by decide+kernel)

private theorem block2:WideCovered band 9383536 9942495:=PRB band Z1.f1155 9383536 9942495 (WB 206367741976 16 0xcf281a359350f0b97b5dfcb2819f4134bc17972d68cb2819a7534572896a4f1cb28195fc3401c0961c7acb1819958b39913959403cb1819578b3471b950b8ccb18191ee33037b948315cb1818dc232afe193fa9ec71818962b25ad0937227c7181854e32152492e9b0c7181806d31bc9a926139c71817e2ab1630991d8c2c708181adb11d3291504bc70817ddcb0d76590c7d4c70817a5730a0a4903f5dc70817618b059548fb6e6) (by decide+kernel)

private theorem block3:WideCovered band 9942496 10990545:=PRB band Z1.f1746 9942496 10990545 (WB 206367775800 16 0xe308134d8d3a3e8d4f67a3c6102581ba6885ea9a8b8f8c204aa874b9ff952c8faf184091ed09512eaa48107e30811b74d24aee146e033be3022749241288a897caf7c6042b6f47298d50a71eef8c084d4e8c740ca03d4fdf18106aed15061d3e58c3be301fed822673fa786dcf7c603da7944929e4e8542ef8c074fe688f9d29bf997df180d53b91353e135d153be30147bf221674e675eef3ca03582f35d1b74c6366e794069f2a6ae1fe983e56) (by decide+kernel)

private theorem block4:WideCovered band 10990546 11548875:=PRB band Z1.f1155 10990546 11548875 (WB 206367775768 8 0xeb2817ae4d7a1dc2c0e32faca05bf4f5c460eaf2a53eb28169b19680e0eb86597aca057ef657f9aaad0877e718155691579972afde279c605284253a479aae69be7181469014796aea756b79c604f9d050601aa8c4bf) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7077824 11548875:=(_Q1 band 7077824 8824574 11548875 block0 (_Q1 band 8824575 9383535 11548875 block1 (_Q1 band 9383536 9942495 11548875 block2 (_Q1 band 9942496 10990545 11548875 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤54)
    (hT0:3968≤T) (hT1:T≤4230) (hnu:7077824≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤12128527754247205:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAY
namespace CZV
open AI AP AN
noncomputable section
def band:Band:=⟨10,55,3901,4203,12617051697948470⟩

private theorem block0:WideCovered band 7208895 8551320:=PRB band Z1.f1747 7208895 8551320 (WB 206367809656 19 0x16db04b28985132a5e09ee62db60962c98a23b07c11b4cdb6c12c026143e4b781f199b6d82574b0286a6df0359356db04ad24050bde3e059e6adb60956fe8a13cfbc0914ddb6c12a6af141eaf780dd9bb6d8253d64282b7bf01313965907ebe6dbc5709a014e72cb20e9a52b049056bfe4ced96419e3c744a68ed7f3f9eb2c830c4ec756680afd6b3f65906092952b614f1f8ae82cb20c01749de49623e8bd1596413f1be201e1ab7c03a4b2c82849ae60033e6f5df4c0c104013dc00e5fe9e76ea017608018980104acbc63d5028410022400141f0769fae) (by decide+kernel)

private theorem block1:WideCovered band 8551321 9116552:=PRB band Z1.f1748 8551321 9116552 (WB 206367809624 16 0xc2f8263cde2d57fae2c6e230be0989a18b4d7f38a9189c2f8260d382d1674e281e2b0be097b2b0b38507897d8bc2f825c9b62cc5dbe23ce32fbe0966fd0b25c9388698dbef82567a02c7b7ee1f7e3afbe0953cb8b1bcab87558fbef82558462c3db2e1b2e42fbe0947138b1299b864191bef824902c2c869ae16de4b0be08fadb8b2d6af852d93c2f82244042d3da5a128e52fba092b3e8ae2269841995b2c835928892395d20e3e5acb20bece29ab8600830597) (by decide+kernel)

private theorem block2:WideCovered band 9116553 9681784:=PRB band Z1.f1161 9116553 9681784 (WB 206367741976 16 0xcb183c40bb15b4793bb78cb183bf4ab1141e933179cb183ba7a30d20592a77ac7183b4b4307d2b921d7bc7183af27b0388991937cc7183acf22ff28991097dc7083b22e2f9c53907f7ec7083adfdaf689c8ff57fc7083a8ee2f246d8f6b80c7083a41daef08d8ee181c70839ee3aebce98e5782c3083986f2e75048dcd83c308391fcae3ffd8d4384c30838d292e07ca8cb985c308395402dba578c2f86c2f8394dcad8da58ba587) (by decide+kernel)

private theorem block3:WideCovered band 9681785 10388324:=PRB band Z1.f1749 9681785 10388324 (WB 206367775800 16 0xdf2830c7c912683d3d06c9be505e0eea23f06a75bd9b8ca0a9ea947658e4e2db471941121fd8fff2b9b476acf382f6b28d5d6dd3466d99e705e7e99a8a74a66a5b73ca0bcf6e34a0034c8fb767941798c668991c98956fcf282f0e34cffa593016e19e505dca219d03aa5e05c73ca0bafbf3351164b7bb9659417492865dfec966d73cb282e6860ca78392bc6e996505c780992561a5565d72c60b99c231e7214a67bb658c1722f2634cae944577) (by decide+kernel)

private theorem block4:WideCovered band 10388325 11518788:=PRB band Z1.f1161 10388325 11518788 (WB 206367775768 16 0xeb283a7d1d6a523ebf0d13aca0e6d295873b1aeaf46eb28393da158537ab66d23aca0e2200542342ac874ae72837cf3148df72adcd339c60dc7ee5083b3aa5f4ee71836df013afbc6a52d439c60d930a4d49dca83752e71835af812f6c829c8d538ca0d42344a6eaea60f56e328346dd5258ad293ed638ca0d204d481636a3e75ae32833f8051c77428b4d738ca0cd7fa46330ea1bf5ee32832cd6917234282ad837ca0c7d3a4519ba9f9762) (by decide+kernel)

private theorem block5:WideCovered band 11518789 11730110:=PRB band Z1.f1161 11518789 11730110 (WB 206367775768 3 0x3bce0f2eed61fafab2fcbeef383c416d7ebbc2c7ad03bce0ed7c35d1b45b0d742) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7208895 11730110:=(_Q1 band 7208895 8551320 11730110 block0 (_Q1 band 8551321 9116552 11730110 block1 (_Q1 band 9116553 9681784 11730110 block2 (_Q1 band 9681785 10388324 11730110 block3 (_Q1 band 10388325 11518788 11730110 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤55)
    (hT0:3901≤T) (hT1:T≤4203) (hnu:7208895≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤12617051697948470:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZV
namespace DDL
open AI AP AN
noncomputable section
def band:Band:=⟨10,56,3837,4175,13324851088604044⟩

private theorem block0:WideCovered band 7339966 8518692:=PRB band Z1.f1750 7339966 8518692 (WB 206367809656 20 0xb6d8462a2c27eb3bf03f8496db08c3b504fba9de06d986db611840c89f3ee3c0b84edb6c2300d413e1487812adab6d845f1d827b5d3f01ca2d6db08bc1144f5335e027d4ecb2175a04ae6cfa3402cc7d9642e85eb5d7a2357fce08b2c85846c6944164afe85036590a58d70e759555fadbeacb216965d35d9dc33f15b9d964245aeaddc33667d1465aeb848ca543c2825af7faaf5d7090308c75a00f5edc742cb211c1f512d43d63d7324d75c2214bc0e16c5379cf3baeb843e3a01ebd436f1705a0bd080163800e36e9de847c16e1001b88010198bb450882742002650013dd8745bf5) (by decide+kernel)

private theorem block1:WideCovered band 8518693 9018758:=PRB band Z1.f1751 8518693 9018758 (WB 206367842392 16 0xc2f84356d01631ae1133b0d85f08686f82c46f522447ff0be10caff4585dc644433c617c2186190aff90487faf1bef842ec5215f60710eded57df085a85a2bea5421b8f8f0be10aa3a8580098432c2e617c2127ae0b12b3885ccd5c2f841bd4c1658a5f0a829d85f08298aa2ca93ca12d71edb61500b11db33e8c21520596426483d256f9dd839eb9b6d8430c4d1421fc90626656db0861f48282cb620b35bedb610c4e905029884143d5db6c218c3a89fefd08241e8) (by decide+kernel)

private theorem block2:WideCovered band 9018759 9590262:=PRB band Z1.f1161 9018759 9590262 (WB 206367741976 16 0xc7185ec0caff5709255f6c7185e5cf2faf6491ca6fc7185df0d2f67ea913ee8c7185e04a2f1d7890b361c7085e320aec88d9027dac7085de08ae927a8f9c53c7085d893ae5c868f10ccc7085d2ab2e26968e8545c7085cc302df07e8df9bec3085c4fe2dba2a8d6e37c3085bcddad83418ce2b0c3085bbf9ad3f908c5729c3085c31aacf6598bcba2c2f85c102acc9558b401bc2f85bab6aca5308ab494c2f85b399ac83028a290d) (by decide+kernel)

private theorem block3:WideCovered band 9590263 10161765:=PRB band Z1.f1161 9590263 10161765 (WB 206367774744 16 0xd338519321aa7314d8732e79c28b18ad3b4066a0b7b3ce144c506914dd33eeaf9e70a1faab4264e996bd0cf285113719d7b84c7024e79428778ecd709a61530b3ca14314d6616792f92779e50a133832b9be973db4cf28506c81933b7cb5916e594281e84c84ff2589a9b2ca1402bc637e492b363f96509fe36b1685f950f98cb18500bbd882e0ca4208e58c27f216c3099a4fe22b2c613eeab60fd5b26da0796309f1dd303a7192e17c) (by decide+kernel)

private theorem block4:WideCovered band 10161766 11269054:=PRB band Z1.f1161 10161766 11269054 (WB 206367775768 16 0xeb285b3239496416afcefb9ca169b8550a673aadcb0e7385988113aa57ea7168b9ce1656474d0b37a8ae94e73858ba092f32d69e5e1b9ce1604f34a9a8ea68078e33857426d244eda95a5ab8ce159e2747ed4ea4525ce33856bf451bb95e8ced3b8ce158b62464291a22440e338556799153c9e8434cb8ce15273c44ea9a9ff624e338538f31136bc27b7c5b8ce147a32457f549dc808e3384e18ed1ae10672c3eb4ce14706b35aed19b99ec) (by decide+kernel)

private theorem block5:WideCovered band 11269055 11911345:=PRB band Z1.f1161 11269055 11911345 (WB 206367808536 9 0x79a428e1b9695a3db5c0b1f3485138f8cd19eb69585dde70a140218dcf82ce5483bce1402163036e4593f09779c27d1865d5799b16704ef384f2b0eb5fdd1609fedd6509d663562d17abce3a3aca138ca8ab2456d710ed759426fc9e541537ad0acc) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7339966 11911345:=(_Q1 band 7339966 8518692 11911345 block0 (_Q1 band 8518693 9018758 11911345 block1 (_Q1 band 9018759 9590262 11911345 block2 (_Q1 band 9590263 10161765 11911345 block3 (_Q1 band 10161766 11269054 11911345 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤56)
    (hT0:3837≤T) (hT1:T≤4175) (hnu:7339966≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤13324851088604044:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDL
namespace DCL
open AI AP AN
noncomputable section
















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DCL
namespace CYV
open AI AP AN
noncomputable section
def band:Band:=⟨10,58,3714,4118,26809193959670747⟩

private theorem block0:WideCovered band 7602108 8259161:=PRB band Z1.f1752 7602108 8259161 (WB 206367875191 18 0xb2c884a87397a62d27e0659b2c883e40814114267d77c2b2c884be4419b10957ce92baeb8829d3a0eda94e7bcbfdaeb8822b688d55dc27b3d66aeb881f5240e3a6967aaecfaeb88102660dfb5227a2038b2c8935d1865117f27991a1aeb881c60c0a1999df9030aaeb8816c2d08c49d5787473aeb8819c618aab0f277e5dcaeb8813f38092dc6df79e91aeb880e1da87e2551775745aeb8808cde883583d770ffaaaa860d61584875bcf6c8aeaaa820acbe040e224763a17aaa860a58504b5434f51ce9a69820975a03183f0748e52) (by decide+kernel)

private theorem block1:WideCovered band 8259162 8642443:=PRB band Z1.f1753 8259162 8642443 (WB 206367876184 16 0xbae881cf3484e99ff41efc5dd7440e5314274051a0e60feeba2071292139a93d06a1e975d1037c9109cab1e8309a8bae881b74904e477741612edd7440d7dcc2725dea09ec46eba2069a70138ff8504678d75d103382709c6f9681ec7abae8818fb784e34a740d297dd7440c07a0271be9a05778eeba205bec4139af75022d3165912d463a72c98a180cf4cb2c88dbb2da35dc8840205ad964443c130b22c0f1fec87acb221a5ace4174660fe470f65910a752f1a3a04c7e94f0) (by decide+kernel)

private theorem block2:WideCovered band 8642444 9025723:=PRB band Z1.f1754 8642444 9025723 (WB 206367843416 16 0xc70883427f0af9cb089b8bbc70882e8880b03b44892a24c708829b9a0b04d13889b8dc7088247630b00dda880cf6b6d83ee12a49ea771877e5fbee883bc510a0a2f886efc8bee883b1cd0a04e8c86a87dbae883a65809ff940866131bae8839f5809fa3088619e6bae8839f9e09f4b7485d29abae8839be309f2390858b4fbae8839c5d09ecb64854404bae8839d3b09e714884fcb9bae8839ea109e147084b56dbae883a0b709db430846e22bae8839bad09d95fc8426d6) (by decide+kernel)

private theorem block3:WideCovered band 9025724 9609770:=PRB band Z1.f1182 9025724 9609770 (WB 206367774744 16 0xcb189239bd712f4c95115658c490082b7a6e6484e4f2c624724f5b76452309f99631231082d833d90f665cb18913e4d6a30d4833e7638c4879e2b47a523f64df1c624253459c07d1e95418e3121505ac9f9c8ebc09c71890a29963d414716b9e38c48670ab0d61a367b731c224246d583bd11a208b8e11207d52bfc938c81aec7088fdb4d5ed21c5f98be38447b6c8af64fe2d92031c223b5cf57862b15abd38e111c2252bb56d8a4752) (by decide+kernel)

private theorem block4:WideCovered band 9609771 10193817:=PRB band Z1.f1182 9609771 10193817 (WB 206367774744 16 0xd34894a9199854dcdc5cce99c4a43d4cab4b26bf40b4ce2514c964bc8534dcd7a6712835b320aa499dfd4d33893dd718d7e8cca89ee79c49d200c5948a630a9b3ce24d7ed620e2730681f9e7126c3530a64097a578cf28936cd582e844b8b716794499b6cc04aa65a212f3ca24c0b05fa6972bf3699e5125913af8c85956b1dcb2892885179fb84a6e436594492548bc10065137bf2ca24819e5d6741277eb19651246152e601f9330c1) (by decide+kernel)

private theorem block5:WideCovered band 10193818 11179397:=PRB band Z1.f1755 10193818 11179397 (WB 206367775800 16 0xeb589e99d530d05d552b0bd6b13b4ff255796aa5e15fad627327a498e8c542d9573ac4dea0c910096a73dfce7589abc551e1f814c419dceb13671ba31e2ca940e839d6269b5745c9da51f33973a44cbcb88b3c4ea2c944e74898352d17c74943582dce912bcaf2333012823ba39d2241b94460c6bcfb8dd6ba44ac82e6a0b449e548cd7489551ecd270bd3b8beba6912a30a1a2145274dd7b4d225355533d67e4e5463e9a44a47a866d09c9c1a30) (by decide+kernel)

private theorem block6:WideCovered band 11179398 12273815:=PRB band Z1.f1182 11179398 12273815 (WB 206367808536 15 0x1f6d1306821d223a6ed225fdd625d2a0b8509a5d17047bac4b265b6c622cb910daf75895b0eed16ce96fe759eeb129a8159418e2db59fbcd225044230ef11dadca879a449ac4b5ec9a1b49c22f34892f55ab87eb166fde9e67124918966074ec9871bbd6246baeab983258a24cf7ac489c0354e70db0276bef5890e65ea61ecb5e147bdeb120b1f943f996b7b43fad623f650a7a6d8d667f0f5ac47a92e4da33cabb2b3) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7602108 12273815:=(_Q1 band 7602108 8259161 12273815 block0 (_Q1 band 8259162 8642443 12273815 block1 (_Q1 band 8642444 9025723 12273815 block2 (_Q1 band 9025724 9609770 12273815 block3 (_Q1 band 9609771 10193817 12273815 block4 (_Q1 band 10193818 11179397 12273815 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤58)
    (hT0:3714≤T) (hT1:T≤4118) (hnu:7602108≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤26809193959670747:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYV
namespace DBJ
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DBJ
namespace DCC
open AI AP AN
noncomputable section
def band:Band:=⟨10,60,3599,4058,27139337404664886⟩

private theorem block0:WideCovered band 7864250 8460840:=PRB band Z1.f1756 7864250 8460840 (WB 206367876216 16 0xb2c8d8ec57b51970460468a2cb2364ff12d85aa6c80d155b2c8d85cf53541a4ae02220acb2331d9726f10a527ff6dbb2c8c85ca611b03da9fd94d2cb231a327437efb7a7ed38db2c8c5d7590c9e2e49f9079acb22a094c07f282007db03fb2b8c391bb88352969f233c6bae30c4b681d77f8a7bfb4aaeb8c29b6b86b1d089eda68ebae309d7161cfe1127ad7fcaeb8c1a791077353a9e91956cb231a6183461d09a79b4aeaeb8c1f8b504c2faa5e48c1ebae28669d610ac828789160) (by decide+kernel)

private theorem block1:WideCovered band 8460841 8759136:=PRB band Z1.f1757 8460841 8759136 (WB 1306953245816 16 0x5ebe307f8c4136fe9685a7605ebe307d2ca1369a7e855e8d5ebe307a90a136750e8515b95ebe30778e81365f1684cce65ebe3075c6e1361fbe8484125ebe30731841367e2e843b3f5ebe3070ea2136727683f26b5ebe306cc661373b5683a9985ebe306908c137991e8360c45ebe3063c72138453d8317f15ebe305f4561385dd482cf1d5ebe305c4d01378ee382864addba305cd201353902823d7658b22a6c75c517cc8981f4a358b22e58712d64c82881abcf58b22befacc85803488162fc) (by decide+kernel)

private theorem block2:WideCovered band 8759137 9132005:=PRB band Z1.f1758 8759137 9132005 (WB 1305879402616 16 0x658c6645bcb06b1245abf2b2c633372d56bff4e2b18fb8e3191f6a2c23c8514692ec708ce7c4d5629b989a2f15f7c688f249e8e684488a52fbe3444bd4f28ce22321dd7df1a22caa77998110ff46bef8d10a653b56888836d05f7c6888a29d3ac043f6fe2fbe3441384e808021e94a57df1a2220a7224710eb8aabef8d0fccd385f108713825f7c6869369c136c4365572fbe3427fe4dea4021a076d7df1a0da626f04110c720ebef8d03051370e4085f034) (by decide+kernel)

private theorem block3:WideCovered band 9132006 9728596:=PRB band Z1.f1188 9132006 9728596 (WB 206367774744 16 0xcf28d4bf4d6cf89ca392a67946a3932b59ec64f82b72ca3505e55a4775269e0d9651a766c2ce21992bd60cb28d3af2965484c915dce59469dbd6b1bd1246684b2ca34f1a45868eb2210d79631a72432c0aea9076c4cb18d33c755f50ac7f28ee58c696cf6af336e3d4ddb2c634995a57669f1d839f9631a397eab83228e3028cb18d118c55bab246cf40e58c684342adcf9234336b2c633f27d570d6d18f66796319d1652bbf5e8be98c) (by decide+kernel)

private theorem block4:WideCovered band 9728597 10325186:=PRB band Z1.f1188 9728597 10325186 (WB 206367774744 16 0xd748d7e6fd947e6cec6616ba46bd0d4c8d60673ec6f4d235d4eb639c5d38d2e9a691ae120b1740e9bd7ced348d6ba2988c3a4da313e9a46b69ecc2ebd26ad2034ce35b0f760d0713445b3a671ad0af302070999132d338d643f97ec38cc7fc5e99c6aff5cbe402a61b7933ce356b065e68292fb87b9e71aab862ee8f3974a97cf38d5503574e2d4b5c78679c6ab644b936a2589d273ca3551cc5c1e0f2b2b459e51aa0ba2dd6dd9503fb) (by decide+kernel)

private theorem block5:WideCovered band 10325187 11294647:=PRB band Z1.f1759 10325187 11294647 (WB 206367808568 16 0xef78d1bec098eb06ac57b7eb68d12ac296330cab3469eb68d0781293144aaa111beb68d0735a90c0b0a8edcdeb68d02e648f3008a7ca7feb68cfac868e34b8a6a731eb68cef07e8caf9ea583e3eb68ce18128d20c8a46096eb68ccb98a8fd47aa33d48eb68c8f5308f3ef1a219fadb58cc929869e242a0f6acd758cc6cf4690e7aa06505d758cc45fa68386a9fd35ed758cc1d6a675f749f41b7d758cc2d6866829c9eb010d748cc145465cdee9e1e69) (by decide+kernel)

private theorem block6:WideCovered band 11294648 12487828:=PRB band Z1.f1188 11294648 12487828 (WB 206367808536 16 0xff78deaceefbfc597d1929f6d1ba2e41e00af6f5a51beda36eda1b974e0de22fc7db46d69b76e815bbb22abfb58d9c404d54aeb73febbeef1b139d599cb76e3703fdde35ef53316d865bdc60fbbc6b8c515ff034b69574f778d64cccba67eb6ae44de6f1aacd616871cad13b63cde353ee52bbf465995c579bc6a2dbf5577b0b2083cf378d3ba06a7033361c9dddef1a601c145183abf0683bde34a825a7a398d74f2977bc69224c4dcbc4ad7b05) (by decide+kernel)

private theorem block7:WideCovered band 12487829 12636285:=PRB band Z1.f1188 12487829 12636285 (WB 206367842328 2 0x3fde3431ab513fb1581a0fbfef1a0301083b2fdbfafe2) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7864250 12636285:=(_Q1 band 7864250 8460840 12636285 block0 (_Q1 band 8460841 8759136 12636285 block1 (_Q1 band 8759137 9132005 12636285 block2 (_Q1 band 9132006 9728596 12636285 block3 (_Q1 band 9728597 10325186 12636285 block4 (_Q1 band 10325187 11294647 12636285 block5 (_Q1 band 11294648 12487828 12636285 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤60)
    (hT0:3599≤T) (hT1:T≤4058) (hnu:7864250≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤27139337404664886:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCC
namespace CZK
open AI AP AN
noncomputable section


















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CZK
namespace CZQ
open AI AP AN
noncomputable section


















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CZQ
namespace CZY
open AI AP AN
noncomputable section
def band:Band:=⟨10,62,3450,3996,28652606475617611⟩

private theorem block0:WideCovered band 8126392 8516619:=PRB band Z1.f1760 8126392 8516619 (WB 206367876216 16 0xbae902d1179d44019207d02eeba405c0a5796f08c81ceddbae91a855fb2b90b2e06a6c2eba4696f78cbd1f93818482bae919b8ccb252138e057d52eba46671dacb1c5a3813a26bae9198dbd336edfee0453e6cb2357920c9756b8a80efcbb2c8d78ac8a9876dc60295becb2340f17c74cd0888010b8b2c8ca61ff11bc0b41fdf006cb2320837638131187ee74ab2c8c6aac98ba354a1f94a4ecb23167b8e27dbb287dbddcb2c8c4d29108ba61e1f4a496bae310b8d21f271e07c946e) (by decide+kernel)

private theorem block1:WideCovered band 8516620 8678421:=PRB band Z1.f1761 8516620 8678421 (WB 206367876216 16 0xbef914c9262874136211b056fbe45af1ceb377a5d8421b9bef916d8db2db782560ff232fbe45a57deb7a365583d75ebef91656a3ae39ca360ec8c2fbe4587384bad4d45838d02bef915e9f2af6754f60d9f56fbe456fbf2c1811ed8342a7bef9159e09b1b8d5f60c75e6fbe4540b00c948fcc82f84bbef913571ab0b2640e0b4c7afbe4448b92b7f198a82adf0bef910a6d1b0a1708a0a230afbe431df6ea3adc31826394bef90b24a62b9c912608f99eeba415d66472dd638821939) (by decide+kernel)

private theorem block2:WideCovered band 8678422 8982988:=PRB band Z1.f1762 8678422 8982988 (WB 1306953245816 16 0x60c240946d013534d48911cc60c240909be1359fd488c770e0c2408b66c13667dc887d15e0c2408718213687a48832b9e1c2407c7f2138a97c87e85ee1c2406b03213c60db879e02e1c24062dba13c2c228753a760c2408b28e12ebed187094b60c2408751812f52c986bef060c24083ce412f81618674945ebe463f3deb2a9088862a395ebe460a352ae565f885dfdd5ebe45d8deeaa935688595825ebe45aad14a7612b0854b265ebe457fd40a4cb7188500cb5ebe4557afea2e521084b670) (by decide+kernel)

private theorem block3:WideCovered band 8982989 9306590:=PRB band Z1.f1763 8982989 9306590 (WB 206367774776 16 0xcf290fc6a95a03c638077b1c64560054ec47e8d6d27c719154f053a970a348b331c645459d4e79788cd870c71914de313979023238571c645284d4e44728c43b9c7191458f9385b122fe57b1c6450b544dff188baf02c709140d1537a68a2d929f1c244fe724dbcc88b1a4bc70913d37936ab1a2b3fc31c244e9fa4d9be48a8594c309138df135c58a28ece70c244d5ac4d68b889f0ddc309131465359972269a0b0c244b19c4d68b4895c27) (by decide+kernel)

private theorem block4:WideCovered band 9306591 9915724:=PRB band Z1.f1764 9306591 9915724 (WB 1305879402552 16 0x699c8c8f14b346832e9a98d33918c4cd654eee5ae255a67230abd2c6f21cb11ef34ce45f64d586897958f27699c8bac06b04b2f29f4e0cf391733d55ecb965196e59e722deb32bbf88c9e88133ce45b5b357118f933c4b679c8b5c08ad4697254f2acf39163fd55a64f6484b799e722bfe02b1ef7c8bf13b3ce453d0956818790e970679c89c258ad99a320a973cf390e6845637e663f00099e5225843aa938e4795a5b3ca4452f85593ac8e9694) (by decide+kernel)

private theorem block5:WideCovered band 9915725 10524858:=PRB band Z1.f545 9915725 10524858 (WB 206367774744 16 0xdb591d139d8de3c504c5d6dac8e60f0c5a9c680100f6d6471a236221e13ede99b6b2380ffb0b15c9eda95d7591bad2183191cf22ef6bac8dae70c0025676c49f5d646dbb15f36af3a38e1ae9236b61af50f79c87b9d7491b0591781d24df981eba48d5ac4bb1e226d79335d24695665cf2c535932ba69233dcc2e2a009a34ded349198a016f7024cd013e9a48cbfdcb66f72642dc34d2465fe75ab2af30ed73a67232f4d2d0da497e202) (by decide+kernel)

private theorem block6:WideCovered band 10524859 11476630:=PRB band Z1.f1765 10524859 11476630 (WB 206367808568 16 0xf38915ccf09877b6af1e96f389150a2095a1d6adf529ef8914464a9382f2accbbbef8913618491b6d8aba24def7912cbf290677caa78dfef7912e1f88e1bb8a94f72ef791198cc8ef22ea82604f3790a1d7c976ce8a6fc96ef790e906e8cf82ba5d328df690f83bc693412a4a9badf690f593a6875eea41503df690f28626794fea3804cdb690efb3a66d5e6a2eb95db690ec6de65f078a256dedb690ea1e26506fea1c227db690ea7a26440b2a12d70) (by decide+kernel)

private theorem block7:WideCovered band 11476631 12694898:=PRB band Z1.f545 11476631 12694898 (WB 240727580696 16 0x81c489aae02010c5f06d5ca06f224c6687a8a3bc08c057fc488be109d4985afd8a5dff322190986fb248be39297fcc8807989adb40ef43eedf7321ec940679417bbe64e7dcc875eb318f856eeaf381f7321cba4c6078b6b993727dcc86e553174f5bee1a811ef321a92de5a8984b740977bcc86637f15fa0fad85ca5ef32192bde5586c4b4edbb7bcc8610c694cb532cf1135e7121773065148b0b29ae079c485a65293dcb12c5c5c9e712167e9c4da820b04804) (by decide+kernel)

private theorem block8:WideCovered band 12694899 12998755:=PRB band Z1.f545 12694899 12998755 (WB 240727580696 4 0x83cc8c2a77a81469719618e0f322df70e97fcc3c531bc81c48acdbea3dfd6710213a07122868ae86d667c2dee0) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8126392 12998755:=(_Q1 band 8126392 8516619 12998755 block0 (_Q1 band 8516620 8678421 12998755 block1 (_Q1 band 8678422 8982988 12998755 block2 (_Q1 band 8982989 9306590 12998755 block3 (_Q1 band 9306591 9915724 12998755 block4 (_Q1 band 9915725 10524858 12998755 block5 (_Q1 band 10524859 11476630 12998755 block6 (_Q1 band 11476631 12694898 12998755 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤62)
    (hT0:3450≤T) (hT1:T≤3996) (hnu:8126392≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤28652606475617611:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZY
namespace DBW
open AI AP AN
noncomputable section
def band:Band:=⟨10,63,3399,3965,28343111664229959⟩

private theorem block0:WideCovered band 8257463 8555550:=PRB band Z1.f1766 8257463 8555550 (WB 206367876216 16 0xbef931377f2fbdc61e0a307afbe4b4111ca21491e82668ebef92bbe8cab815cba0903feeba4975902739fdb5821b6fbae9231d9c9dcb4f7607d782eba4ee1860c6a352c81d050bae93b5e7cb1de99d206ab02eba4ed0f82c8e744c818530bae93b375432bffab2057e86eba4ea920ec975b44813a11bae93775acad05f1ae045206cb23723848be4d28280eef1b2c8d8be77a9f2c7c60162cacb23393356633f2b87fc273b2c8ca3dd690baa521fcb0d2cb231dc84a3131f507e95f5) (by decide+kernel)

private theorem block1:WideCovered band 8555551 8709402:=PRB band Z1.f1767 8555551 8709402 (WB 1306953245816 16 0xdfbe48808a812635ec84e51adfbe48792e8127bd5c84bf8adfbe486e75e12a1b348499fa5ebe4e14546b242f0b84746a5ebe4e01932b2167fb844edb5ebe4df01fab2443a384294b5ebe4ddffd8b2d894b8403bb5ebe4dd141cb3e59c383de2b5ebe4dc42e2b58814383b89c5ebe4db8f9eb7e2efb83930c5ebe4db0332bb2f82b836d7c5ebe4daa6dabfb9cd38347ec5ebe4da8720c5f206b83225d5ebe4d65de8c49aa2282fccd5ebe4d1fdfac43135182d73d5ebe4c6911eb3e7e8882b1ad) (by decide+kernel)

private theorem block2:WideCovered band 8709403 8969026:=PRB band Z1.f1768 8709403 8969026 (WB 1306953245816 16 0x62c6489160e133a3a688db42e0c6488c54c134294e889022e1c248855a41352836884503e1c24878c4e137b82d87f9e3e1c2487b7501341a0187aec460c2488d22212ca4908763a4e1c2486ea8c133dcf08718855ebe4e79b3ac73cfc486cd665ebe4df3450be00dbc8682475ebe4e7dfdcb08525c8637275ebe4e40e02ab9c16485ec0860c248806c612be67b85a0e8dfbe487fcc412af89a857b59dfbe487bfba12b7fea8555c9dfbe487c1ba12a32f9853039debe4883fe0125e020850aa9) (by decide+kernel)

private theorem block3:WideCovered band 8969027 9276729:=PRB band Z1.f545 8969027 9276729 (WB 206367774744 16 0xc719365f59374fc46c69ce38c9b16c49b6ece3508671c64d7d584d922b19edf58e326b71e26b6ad8cabdac719357d253573946305de38c9a9b109a73e630566f1c64d3a124d17b51794f98e32696aba686dc8b7f5dc71934956133ba7c59a1f638c9a394a99a17e2ba47b1c64d0e054cd115153bff8e1268159265c538a52dfc70933d779328c1c503e0638499be38996c6e26f2831c24ccc574cacbb12e3038e1265ad6a6554a892661) (by decide+kernel)

private theorem block4:WideCovered band 9276730 9872903:=PRB band Z1.f1769 9276730 9872903 (WB 1305879402584 16 0x699c9cd44eb07f1496a607699c9c980aaf8b60960fc8699c9c5ad4aef548957989699c9c137eae620c94e34b679c9be736ad8558944d0c679c9bc1cead1ccc93b6cd679c9babccac3e2093208e679c9b71d6ac0d00928a4f679c9b1b94ac233c91f410679c9ad762aba47c915dd1679c99f0b8acf6a090c792e79c977f82b17f58903154679499fce4a841738f9b15679499544ea91ba68f04d6679498c7a6aa64a58e6e97638c9b47469be5f88dd858) (by decide+kernel)

private theorem block5:WideCovered band 9872904 10488309:=PRB band Z1.f545 9872904 10488309 (WB 206367774744 16 0xdb593dd391861a3d004faedac9ebd8cc1cc3e7dcedb6d64f47a460457f3dbaefaeb279630afbf349e4739d7593c49f57b6944ed87d6bac9e25cabc688a746aef5d64f170e5d612d3908f9ae927814f2e717a9bee3dd7493bb13d71722cdabff6ba49da66ab789966b06ff5d24eba595b482f345701a69274e11ad50e5999542d3493a4da9688e3cc7f81e9a49d21f2b34a2661a3134d24e959658f02b2fa50ba672741372c4944973c46) (by decide+kernel)

private theorem block6:WideCovered band 10488310 11334492:=PRB band Z1.f1585 10488310 11334492 (WB 206367808568 16 0xf3893549ea9301d8acf35cf389347a5092019cabc6dfef89334516906ee6aa9a61ef893245668fa15ea96de3f3892fccb891f87ca84165f3892a0b6e9666d5a714e8df79303f3469e7e6a5e86adf7930340468f4daa5522bdf69301edc67f44aa4bbecdf692ff13c673080a425addf692fc262666cbea38f6edf692f8c6e658464a2f930db692f5a1864bdd8a262f1db692f233863e656a1ccb2db692f276e63026ea13673db592f195c624770a0a034) (by decide+kernel)

private theorem block7:WideCovered band 11334493 12565304:=PRB band Z1.f545 11334493 12565304 (WB 206367841304 16 0xffa932851f75d526bfbb38ffa9318c597056a9be8ebbffa93105716c240dbd623dffa93046be6802a1bc35bffba92f8c62640b3fbb0941fba92efb7c6032f3b9dcc4fba92e91995d8b62b8b046fb992e02015aa44cb783c8f7992d716557cfe1b6574af7992d250f551e85b52acdf7992cc9f553477ab3fe4ff7992c56e4513b3cb2d1d1f3992bdeb54f3ae2b1a553f3992b79964dc1f5b078d6f3892b720f4c064baf4c58f3892b106f4ab6b5ae1fda) (by decide+kernel)

private theorem block8:WideCovered band 12565305 13179990:=PRB band Z1.f545 12565305 13179990 (WB 240727580696 8 0x85d49f25f12f6ed1724715a0f3278824cb19c86c7f2a983cc9d054ba91a6031b18ae0f3271348c9a862ac599ad83c49b84d3a452ef711b4be07326b2ebe88d2d3c340b281d49a3f57a0487770850d207526711607ba234c0e7b6) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8257463 13179990:=(_Q1 band 8257463 8555550 13179990 block0 (_Q1 band 8555551 8709402 13179990 block1 (_Q1 band 8709403 8969026 13179990 block2 (_Q1 band 8969027 9276729 13179990 block3 (_Q1 band 9276730 9872903 13179990 block4 (_Q1 band 9872904 10488309 13179990 block5 (_Q1 band 10488310 11334492 13179990 block6 (_Q1 band 11334493 12565304 13179990 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤63)
    (hT0:3399≤T) (hT1:T≤3965) (hnu:8257463≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤28343111664229959:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBW
namespace DBV
open AI AP AN
noncomputable section




















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DBV
namespace DAX
open AI AP AN
noncomputable section
def band:Band:=⟨10,65,3301,3899,29721485741079288⟩

private theorem block0:WideCovered band 8519605 8676592:=PRB band Z1.f1770 8519605 8676592 (WB 206367876248 16 0xc309726f54ec72037108c9e17df2dc684c3138dbde10fa76fbe5be16146cef723420c24df7cbc9327d64ccd1583f1f5bef97890f1ac5570eb0797437df2f10efb5a52c7d60e953afbe5dfdfd6b4a7d52c1bf7d5f7cbc017cd73e7ab58358a6bef97827fab04c19eb0664a57df2ee2b635ff6db120c2ffefbe5d67deebc8e119c172d5df7cb9c96016a8d52282bf57bef972b2bd2edbffc50532077df2dd00b650ee30c609cac2fbe5b37a7ca852b10c1262e5d74b36a4c0e69adf0822608) (by decide+kernel)

private theorem block1:WideCovered band 8676593 8931697:=PRB band Z1.f1771 8676593 8931697 (WB 206367876216 16 0xc7197077922a98bf122125c70c25a31c3277a00fa87fcc9c3097d0ac530646cae1ec08b0c25ef136abce30b387637ac3097b9a7c3020c32e1c5b4f0c25e9f748bead3eb86ca2bc3097ab60732131eee19f6130c25e745a8ccab56b8630ddc3096a6e8915c0156a1790db0c25a8415857d89ca85bde2c309738ce72c65f7a6165e3b0c25c94fe0b29e70985713bc309719de9af2464c6152b9f0c25c2ded6cc39301852493bef97892e92888b62213f8fefbe5df34a8a00606884b198) (by decide+kernel)

private theorem block2:WideCovered band 8931698 9245672:=PRB band Z1.f1772 8931698 9245672 (WB 1306953245816 16 0x64ca58a442413398f68d13e864ca58a153c133a0968cc740e5ca5876f1413dcfde8c7a9964ca589cb38131ee158c2df164ca58984ca13240658be14ae2ca589897e12f952c8b94a2e3c65892e5e13020d48b47fbe3c65887f7e132689c8afb5462c65f28420bda0fb28aaead62c65efa574bc479a28a620564ca5c6a57bb64de138a155e62c65eb7b36be6fb0a89c8b662c65ea6ad6c333aca897c0f62c65ea1ed2cbb6afa892f6762c65e0c6d6c5b014188e2c062c65d67072c157060889618) (by decide+kernel)

private theorem block3:WideCovered band 9245673 9559647:=PRB band Z1.f557 9245673 9559647 (WB 206367774744 16 0xcf2977dafd3a45748ef2fe594bbe51c9cb6ee4646df2ca5deb494e3cad228a219652ef33627050490f868cb29777b4537a47c855e0e594bbab989b9c96417c672ca5dd1094d96bd2024e59652ee33926bf778fc5cbcb297705cd3517447bc926594bb69209a645a3cb1f32ca5dade24cfd2d1dbfab9652ece522676dd8e932dcb2976199933b014723436594bad75899ab4237e77b2ca5d4f7d4cddbd1b5a6f9652e9d89a667c38d608f) (by decide+kernel)

private theorem block4:WideCovered band 9559648 10167972:=PRB band Z1.f1773 9559648 10167972 (WB 1305879402584 16 0x6bacbde55eb2bb209b26a46bacbdda66b1a9849a8d556bacbdd186b0929099f4066bacbdc278afa4c4995ab86ba4bd877eaf379898c1696ba4bd3f50ae9cf098281a6ba4bceb9eae1298978ecb6ba4bc87f6ad9dec96f57c6ba4bc2eeaad46fc965c2d6ba4bbe372ad1b7895c2de6ba4bb72b8ad5cd495298f6ba4baa366aeb7949490416ba4b9e328aee0b393f6f2e9a4b9efc8aba7be935da3e9a4b7ad10af4fe192c4546794bbfaa89d6388922b06) (by decide+kernel)

private theorem block5:WideCovered band 10167973 10795922:=PRB band Z1.f557 10167973 10795922 (WB 206367807512 16 0xdf79705db4c751de92ee4b7de5c0c7431668ea42243df79703370c3d9f68e23d37da5c065db09379a2efa6df696fe5fec0f05a89595f7da5becc0afed05a1bd08df696f7db2be7cfa848ee76da5bd0642f46b6a08a6adb696f1592bbb3667fc46f6da5bc50f2e911a9f57ccdb696f16bcb8cafa7af9f76d65bb940aded879e252fdb596eb184b6c242762f836d65b9edfad790e9cf291db596e3c56b4d74e71650b5d65b7d9eacf27c9bbff3) (by decide+kernel)

private theorem block6:WideCovered band 10795923 11737846:=PRB band Z1.f1774 10795923 11737846 (WB 206367808568 16 0xf7a978dd3c9cfbb4b31af6f7a97860649a8f26b1e858f7a9782aa69796c8b0b5bbf799773e7e959990af831df799764bfe9501ecae507ff79974ff0a9517fcad1de1f79972eccc96b696abeb44f7996e215697c983aab8a6e78971dd4c6ad9a4a98608e389719d3469d64ea8ecb9e389715e0668d02ea8536ae389715f3e67c660a7ba1ce379713d3a66dea0a720cde3797106b666097ca6877ee37970d1ae65468ca5ee2fe379709a6c64819ca554e1) (by decide+kernel)

private theorem block7:WideCovered band 11737847 12993745:=PRB band Z1.f557 11737847 12993745 (WB 240727580696 16 0x83e4bc350aa3a1f4b1913460f92eda00c85f4c8c5123383e4bae0471fb6ca30f7e5a0f92e96358795a71c2acf881e4b9c8ba1ce013705e96a0792e595346e0ee2c047bc81dcb9045c9a91a82fc547dff72e268ce6622f8bde2817fdcb8317d188976ef2bf8dff72dfed665e9743bb7d457fdcb7b4c59705a66e92aa1f772dd8e865935fab9180a7ddcb710969599976df95b5f752dc00585444f5b6b2cf7dd4b6c1b19494312d600c9f752d9fc4e505ef5b44d94) (by decide+kernel)

private theorem block8:WideCovered band 12993746 13542460:=PRB band Z1.f1775 12993746 13542460 (WB 240727614552 7 0x25692d3aa2341f00c2cea43c93dcba91ac55d0f58735d20e1f72e38fee3340f90cc41e587d4b82dff8bd5e4632c3d221752ddf9272b91008c9dcaa85e4b6f65dca11376322a8361792da249825f7198c7776f) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8519605 13542460:=(_Q1 band 8519605 8676592 13542460 block0 (_Q1 band 8676593 8931697 13542460 block1 (_Q1 band 8931698 9245672 13542460 block2 (_Q1 band 9245673 9559647 13542460 block3 (_Q1 band 9559648 10167972 13542460 block4 (_Q1 band 10167973 10795922 13542460 block5 (_Q1 band 10795923 11737846 13542460 block6 (_Q1 band 11737847 12993745 13542460 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤65)
    (hT0:3301≤T) (hT1:T≤3899) (hnu:8519605≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤29721485741079288:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAX
namespace CYH
open AI AP AN
noncomputable section
def band:Band:=⟨10,66,3254,3865,29906389501753189⟩

private theorem block0:WideCovered band 8650676 8848870:=PRB band Z1.f1776 8650676 8848870 (WB 206367876216 16 0xc3099c0ff72faa3de61c179b0c267019a6c50469986b87bc3099b7434b277962619ac3f0c264d1d0e96a1ac8861da4c3098a61fc957b5d7a1740e30c264fb9dcab00f4d85a983c309937e792c8fe596160b370c2648f6e0b5556ed855c17c30991824230d03af614d5870c2640ac2ed59c5a4850eacc3098c600cb623164e139fdb0c2617ba88bce3c7284c140c309810070e4a93026126a2b0c262c0f5b9dff5798473d5bef98e8b6c9844bb2211347efbe639a954618a698842669) (by decide+kernel)

private theorem block1:WideCovered band 8848871 9165981:=PRB band Z1.f1777 8848871 9165981 (WB 206367876248 16 0xcb298b11469566965517b93b96532c42485afa00662e3ccb2ca654aae4c233c3cc5a0e36594c99675da7494088af45bcb298b77fc2eb9a6cf154ddf9653024b8e4d48381a2966131c663a83086283e92c5060c638ccdcde717c7131489beadc7199ba278b16194a912e2838e33350c4463846f12248f5b1c6661906cc3beac1c46b35638cc8f62cd3da40328888ffc7198fbae429187e451077298613101ba83a7cdd061fb8a70c267603f2bef514843d05ee184ce409c57912690875352) (by decide+kernel)

private theorem block2:WideCovered band 9165982 9483092:=PRB band Z1.f1778 9165982 9483092 (WB 1306953245816 16 0x66ce60b5df6135c3fd90b35466ce60b3fc413584559065e966ce60b1d94135559d90187d66ce60ae9cc135c2e58fcb1266ce60ab9de135d0dd8f7da666ce60a80a613605ad8f303b66ce60a3aca1366e7d8ee2cf66ce609e2ee13721358e956466ce609748e137fe0c8e47f8e5ca60965b81359f738dfa8de5ca608b6a0137994b8dad21e5ca608f96a132f9d28d5fb6e5ca607cec4136ae1a8d124b62c667da96ebafea618cc4e064ca638014862984608c777464ca6361986632fef08c2a09) (by decide+kernel)

private theorem block3:WideCovered band 9483093 9879480:=PRB band Z1.f1779 9483093 9879480 (WB 1305879402584 16 0xebaccb2a4aaf95c896bfb8ebacc94bfeb2e4e89624e16baccb0a24aabb52958a0aebacc6c200b327e594ef33679ccc93ec9e217494545d679ccc8afc9db6f89406f2679ccc82369d4af093b986679ccc79aa9cdd20936c1b679ccc6eba9c7ec4931eaf679ccc5f509c396892d144679ccc45329bea509283d8679ccc21229bac7892366d679ccbfa0c9b718891e902679ccbcfe89b4080919b97679ccba4229b356c914e2b679ccb78ee9b08e09100c0) (by decide+kernel)

private theorem block4:WideCovered band 9879481 10513701:=PRB band Z1.f562 9879481 10513701 (WB 206367774744 16 0xdf699ee3c573498d03692efb4cf3042b85eb67f493b6da6778275bb78f3e6eefb6d33b5d12d88ef9e9ca0db699da22569a07cf00e56db4cec2c0b3e2ca759bcf6d6675394595aa9399839b6b339b58ac88c39c3145db599c4aed6286acdcb37edaccdd402b069426bee636d666bf4e58038d34c183b6b3352beabd1cf99c5eadb599a16555e48bcc9589ebacccd250ae993e6240f35d666447157190d2feacbb6b32fa5aabbf30975a8e) (by decide+kernel)

private theorem block5:WideCovered band 10513702 11147922:=PRB band Z1.f562 10513702 11147922 (WB 206367807512 16 0xe78992432ed26952a86a4b9e2648210342a39a97fbbe78991c814cebf4aa393938e264631eb34814a84a0de389914768cb2de29ebcdf8e2644fbd324f2ca71460e3799135c2c7969e99e6278de643f53b1811da5deb2e37990c90cc4ba52950f738de6422fab0c940a4a905df79904b90c18ade9038bb7de6403adb00f8fa37357df79900cb4be97d28b62037de640217af50f3a23da9df698fe1bebbe06a868b4b7da63ea142ea6d7a107fb) (by decide+kernel)

private theorem block6:WideCovered band 11147923 12297448:=PRB band Z1.f1780 11147923 12297448 (WB 206367808568 16 0xffc99fa6c2b92f96bba4e8ffb99f10b0b35958ba6f3bffb99df9b2aede1cb9398dffb99cb16ca9989eb803e0fbb99b87d6a580beb6ce32fbb99b0fdca19754b59884fba99a836c9e9dfab462d6fba99997a49c5720b32d29fba9985ea6994d28b1f77bf7a9971f8297ffdeb0c1cdf7a995745c97d242af8c1ffba992bfc29a267aae5672fba98c2e869fde6fad20c4e79992a9b26c3d40abeb16e7999285b26b3c54ab503fe789927cfc6a169eaab568) (by decide+kernel)

private theorem block7:WideCovered band 12297449 13565890:=PRB band Z1.f1781 12297449 13565890 (WB 240727614520 16 0x95e4c704aa932e60ae77fe143ee64c70e46ad971b3728561f9322a0a330a1a2d9928cf0fd990080b1664ee6cb5eba87ecc76c1f4a6a5be65148642f6636b2844d28beb23cd7a17b319c3db24208458f7b610bd98c21551118244c6880383ecc5b6e008199ca62a92ac1f662b11503d7835b1072a20fb3149a581d2b65585cdf507c989cf100dfa91cc1b14d81e4c4aa9cc6b3d6c603dcfc0f2624232a336ce32fd17c6079311474118c575d7c2086ffc98844ef8bf65e0bcda96) (by decide+kernel)

private theorem block8:WideCovered band 13565891 13723695:=PRB band Z1.f1782 13565891 13723695 (WB 240727580728 2 0x25713253d8af8ba67e8b417caf667cbff5fa747ed03570) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8650676 13723695:=(_Q1 band 8650676 8848870 13723695 block0 (_Q1 band 8848871 9165981 13723695 block1 (_Q1 band 9165982 9483092 13723695 block2 (_Q1 band 9483093 9879480 13723695 block3 (_Q1 band 9879481 10513701 13723695 block4 (_Q1 band 10513702 11147922 13723695 block5 (_Q1 band 11147923 12297448 13723695 block6 (_Q1 band 12297449 13565890 13723695 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 10)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:10≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤66)
    (hT0:3254≤T) (hT1:T≤3865) (hnu:8650676≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤29906389501753189:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYH
namespace DCP
open AI AP AN
noncomputable section


















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DCP
namespace CYC
open AI AP AN
noncomputable section


















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CYC
namespace DCK
open AI AP AN
noncomputable section
def band:Band:=⟨11,46,4298,4349,9161968566745543⟩

private theorem block0:WideCovered band 6029255 9483627:=PRB band Z1.f1783 6029255 9483627 (WB 211735337048 23 0xc418735c62f4c6af90b56bc017f358aef321879033acc017f354cef176c38fb1edc017f3502aef5dab8f302ec017f353eaedad5f8eae6fc017f350e2ec59778e2cb0c017f34d56eabe0f8daaf1c017f34a14e96c0b8d2932c017f34636e7c70b8ca772bc17f34280e65e638c25b3bc17733e9ae4fc578ba3f4bc177339d2e326438b2235bc17733cc6e1ab438aa076bc17733cc6e09b6b8a1eb7bc1773393edf3af7899cf8bc17733600de2f2f891b39bc17733280dd239f889979b817732e24dbaedf8817bab8177329f0da9a5f8795fb05eaf2018601ec0287143c068a7200e601181d86927d060a7200a400adf4848b800400f200bc00acf87c6f8e) (by decide+kernel)

private theorem block1:WideCovered band 9483628 10280230:=PRB band Z1.f1784 9483628 10280230 (WB 206366628952 15 0xdaae7e0a562cb6c9cdd26daae7c8015ee66c9bdbd8d6ae7a5d159348c9ad85ad6ae7848d56a74c99d4dcd6be74f3551e5d898d15dd6be7827d4ea32497cddfd6ae65d6153345096ca61da9e4efd360a6ea95c6e3d6ae6fd6d598c7194c364c70e6da08ffe62893bfe6c70e6d194fde14c933e27c70e6d5b4fbd67092bc68c70e6ce54f9f068923aa9c70e6c7b0f857e091b8eac70e6c0d8f6bdcc91372b) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6029255 10280230:=(_Q1 band 6029255 9483627 10280230 block0 block1)
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤46)
    (hT0:4298≤T) (hT1:T≤4349) (hnu:6029255≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤9161968566745543:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCK
namespace DCY
open AI AP AN
noncomputable section
def band:Band:=⟨11,47,4215,4324,9396426721297806⟩

private theorem block0:WideCovered band 6160326 9319394:=PRB band Z1.f1785 6160326 9319394 (WB 206366660696 23 0xc2feac5a8e4f8a78e33e2c2feabeeee3b0138db09bc2feab7e4e265938d2d54c2feab07ce1185b8caa0dc2feaa89edfc6d78c26c6befeaa034de6fe38ba37fbefea9718dd11278b2037beeea8d20dba7db8a9cf0beeea8f94da30e38a19a9beeea94acd8bfaf899662beeea8d8cd7b8a389131bbeeea85e0d6b17f888fd4beeea7d80d5a91f880c8dbaeea7442d49eab878946baeea69ded390ef8705febaeea5df8d27d9f8682b7badea5004d1622b85ff70badea523ad03aaf857c29badea6708cf515b84f8e2badea5d34ce3d3384759b064e8037e01e53683f254063e802220113e182ebc5047e8019000aad47ed18c) (by decide+kernel)

private theorem block1:WideCovered band 9319395 9924322:=PRB band Z1.f1656 9319395 9924322 (WB 206366661688 16 0xdabeb0f2aa9bc44976ee2dabe9e9f8ad3039966854cb1eb1bce7f07a09561c6cb1eb13ba7e189694de7fcb1eb0b687d2784945b38c71eb01ec7c0f1e93d7f1c70eaf8be7b0cd29354a9c70eaef627a0ee292d162c70eaf5207916ba924e1bc70eaee0878508291cad4c70eae6b877893891478dc70eadf2476c03e90c446c70ead73e75f4dc9040ffc30eacefa7526968fbdb8c2feac63c7454208f3a70c2feabbc4734ba88eb729) (by decide+kernel)

private theorem block2:WideCovered band 9924323 10461465:=PRB band Z1.f1660 9924323 10461465 (WB 206366694424 8 0xdabea23f65a22e39fa119dabea15875913049e9cc5dacea14d456fa009d9637dacea083b55f7479c8fa9dace9fa9d551b189b891bdace9eb265475689a828ddace9d82c542792997bffdace9b8065370ad987571) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6160326 10461465:=(_Q1 band 6160326 9319394 10461465 block0 (_Q1 band 9319395 9924322 10461465 block1 block2))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤47)
    (hT0:4215≤T) (hT1:T≤4324) (hnu:6160326≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤9396426721297806:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCY
namespace DDO
open AI AP AN
noncomputable section
def band:Band:=⟨11,48,4136,4299,9718602346092229⟩

private theorem block0:WideCovered band 6291397 9113322:=PRB band Z1.f1786 6291397 9113322 (WB 206366660664 20 0xbefefdde4d931bb161dd57dddf9c35af6eb62a286efbbbf0d235a8b3c502a65f777ee2a6aa6b389807cbeeefd11ed43e6311f75b7dddf89f9a65bc621db7afbbbededb486b4c3f907df777d47c6881e5876d40baeef99f2d0442b0dd0e375ddf0ebd9e8b76198e8aebbbdc36338870c2ef69dd6f7b171667729855a03badef9480cbb70f09aa6975bdf0d359605ce114196eb7bdda9b295d8c1e5cb5d6f7b31c651f398346c7badef4fc2c9bd670583f175bde66fd92ac8e08f4a6eb7bc3893245bbc0dc2d0317602a800ef7481338a) (by decide+kernel)

private theorem block1:WideCovered band 9113323 9657307:=PRB band Z1.f1660 9113323 9657307 (WB 206366693400 16 0xc71ee3a2e7929ff26b7b78e1dc65dcf04c2e4b5c331c3b8c725dc6e949291ee3877189a3b22b791cd6dc70ee2bcb7587b322913d8e1dc4cb8e9a40e430f3f1c3b880cdd001fc81f80618770cde3995a08fba31c30ee12e57251371e6ac585fdc1736e2e2063ac24f0bfb84b05c224dc715e2617f7071db803b78da6f5c2fee08bb6f5d5b1a444d85fdc05dadd629e32755f0bfb7f309b80a2c60c445f7f6fb1136a8118b93b9) (by decide+kernel)

private theorem block2:WideCovered band 9657308 10575282:=PRB band Z1.f1787 9657308 10575282 (WB 206366694456 16 0xdedef683e5ca29650aed96f6f7a7532d6684a8150536b7bccd8963ff093e94edb5bde35c2afa6a69e40d8dadeef87a5619fb4e9b9d6d6f7843caa68f8270b6736b7bbda0951e0853647fdb5bddb792a7a7ce9a1a5fdadeeb94d5395d44c8860ed67746a0aaa0412601c8f6b3b84471549c132dfb0b963dcb3d07dda9295f3e6cb1ee53c33e73184ab78be58f726bb1efbffa53a9232c7b91f38f646a128caf38e3dc823e7a28b293e0aa) (by decide+kernel)

private theorem block3:WideCovered band 10575283 10642700:=PRB band Z1.f1660 10575283 10642700 (WB 206366694424 1 0xdedef78ae5da765a2650c) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6291397 10642700:=(_Q1 band 6291397 9113322 10642700 block0 (_Q1 band 9113323 9657307 10642700 block1 (_Q1 band 9657308 10575282 10642700 block2 block3)))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤48)
    (hT0:4136≤T) (hT1:T≤4299) (hnu:6291397≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤9718602346092229:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDO
namespace DBP
open AI AP AN
noncomputable section
def band:Band:=⟨11,49,4059,4274,10022184552707145⟩

private theorem block0:WideCovered band 6422468 8898625:=PRB band Z1.f1788 6422468 8898625 (WB 206366693496 25 0x2fbbc9a7f598f55487c841beef260de65e81f21d07aafbbc955c595b1fc86bb93baef247e764e65f218d4f2ebbc8e55d929a3485aee5baef22559641e61214a23aebbc835f58fc78484a237badf217f56366bf2106f82eb7c8d43d8b2ce4839588badf2230462d9cf20c3cc6eb7c886358a331c8288dabaef1847863e1872080a0eeb7c7bcdd89b15e817c2cbadf1c2ba622dc3603d756cb3c875956c47f4806f7eb2cf2288e5ac5bd200b14ecb3c8a7a16a32447fe927b2cf226545a5cb11fe97f2cb3c88c0d68fe047f62d0b2cf21f075a0f991fc7e9419fc00e0003b2237edc7906af002240086709f9588816fc008c40218897d4974052f001870053081ecc05c107c00618014a6072caa6) (by decide+kernel)

private theorem block1:WideCovered band 8898626 9448883:=PRB band Z1.f1665 8898626 9448883 (WB 206366693400 16 0xc70f2c336708943205b678e1e5752cdf75263e9d730c3cac685bbbaac79082e1879546db71f488e9aaec2ff29e516d5ee11c28af85fe556a4d95a9a3638030bfca912db01a64683d4e17f94e7335b8328c8152c2ff295346ae0bb17f5f585fe51870d467a62dd28efbfca0ea5a6d664577265f7f93c723480288a67f5beff26db168692713c33d7dde4e366cf75da256d1efbbc9e9659c58cc46a785f7793991b36061884e99) (by decide+kernel)

private theorem block2:WideCovered band 9448884 10067922:=PRB band Z1.f1789 9448884 10067922 (WB 206366694456 16 0xdadf2821d53f20b4ccfe96f6f84aac6adb70e624c932cbcc75c8fa3b8d2f0ced965e626f47bfade97001fcb1f30a593d81604b3ce4658f981f01e754ea57cdc72c7cc17fcf1fc2d2ada35963e5fb747810d894e6c3cb1f2f5343b90794a3035e58f976bb1d964e24f68531c7cb912ceac5cd26a77b8e3e5b7ba74967892cd66c70f2d1c639cad9492387e38796c689ca517a4702e31c3cb48e4e3e7992274c38e1e594ba712a8e90b40a) (by decide+kernel)

private theorem block3:WideCovered band 10067923 10823935:=PRB band Z1.f1665 10067923 10823935 (WB 206366727192 11 0x71779322f180ebba94a3ff8bbc95604bd5309483d3fbdde4860e5caf61a311f1deef22f5e2d5fa15102a1ef77917b9563ed5683e2577bbc8853caf721d3fd7cfbdde41da256086f9edf39daef1fdb7aa7e9b4ee945ed6f8f4b2d5099867317736b7c73aa6a74e3b37725db5be349cc53de9a9aac80) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6422468 10823935:=(_Q1 band 6422468 8898625 10823935 block0 (_Q1 band 8898626 9448883 10823935 block1 (_Q1 band 9448884 10067922 10823935 block2 block3)))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤49)
    (hT0:4059≤T) (hT1:T≤4274) (hnu:6422468≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤10022184552707145:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBP
namespace DDQ
open AI AP AN
noncomputable section
def band:Band:=⟨11,50,3985,4248,10347035358042453⟩

private theorem block0:WideCovered band 6553539 8779654:=PRB band Z1.f1790 6553539 8779654 (WB 206366693496 34 0xbeef6bc8e62b96b217de1afbbda9bc58953d4856fa7beef68d49623ab12139f22fbbd9a41587f2d4845fe9beef6353d61f1d920f602afbbd78b1989a0bc83502bbeef5862f62abb320b2132fbbd42a018b5c9582406db6cf69f645a15b9206e23adb3da6695678f5481749fb2cf692d0599a79204c2becb3da30796598cc80ecc0b2cf684d9593119202a342cb3d9f39963eba48064e1b2cf67ea058c34d20083c6cb3da14856229347fdd02b2cf692f8582f851fe644acb3da55055ff8947f5523b2cf6908957dac71fc44cecb3da2e015ee0047ecd44b2cf6861a5795c11fa2552cb3da01155dd04c7e4565b2cf67948573c271f805d6cb3d9c9655c6b8c7dbd85b2cf66ab756fa5f1f5e656cb3d988fd5b6c047d35a6b2bf658c456bca11f3c6dacafd936a55a46cc7cadc7aebf640d85662031f1a75c17bd0115c03a5e37c25e8069f4044900e97c9ef87e0187d00aac0211d97b5a19058f401db0051e81e4ea74107d0077c0146a074fba4) (by decide+kernel)

private theorem block1:WideCovered band 8779655 9336183:=PRB band Z1.f1671 8779655 9336183 (WB 206366693400 16 0xc30f733956b192f1ceaef861ee4fc0d4e8ea37b6630bfdc84eda650446b2dce17fb97603477568cdddac2ff7263268761118abf785fee3754cfa3622f38730bfdc46b99d651c5a31ee17fb835cb371038abe5ebeff6f8e4663423146cff7dfedd5e4cb740e26ba82fbfdb6b2594ff1449360df77b7340b23d5f889ee2beef6f29663ffcb102e077ddedd070c76b8e1e3c92fbbdb6b698ceaec383a2df77b6697317dd5867f66) (by decide+kernel)

private theorem block2:WideCovered band 9336184 9892712:=PRB band Z1.f1671 9336184 9892712 (WB 206366693400 16 0xcb2f7b4bb78378f2de6d1965ef50aeee428659ae272c7de72c5d8b99caf1d5658fbd0973a8dd6955bcbcb1f7997374476529a7d9963ef2086e70f8a5130372c7de1609ca7d849e217658fbbdbeb8ecd5933c4fc71f7710f71141f2568e18e3eec92ce0374648b2471c3dd6339bd32c48d2596387bb2ec3742a1911cd3c70f75c1e6dc2012129e98e1eea660da4a324034571c3dd2729b21fe47c29b6187b9f30b5ddbd8efd57) (by decide+kernel)

private theorem block3:WideCovered band 9892713 10866638:=PRB band Z1.f1791 9892713 10866638 (WB 206366727224 16 0xe2ff6df6c2f6294a973f3b8bfdb66c2b91d0ea4c010e2ff6c7082d856ea8ec14b8bfdac04cb25950a2a094deff69725abab05a86435b7bbd9ffa2ac5dc4a08118deef6882baa4447a7dc5677bbd9d294a701b69e619bdeef66337a9ac2ca7547777bbd91ffaa5e9529c421fdeef6210ca9a01826cc9877bbd74faea77d5b9a22a3cf2f5efb51f02912644b973cbd7ab0a7b23ae988b06cf2f5e50a1e848ba600c9f3cbd77f547928d2977b48) (by decide+kernel)

private theorem block4:WideCovered band 10866639 11005170:=PRB band Z1.f1671 10866639 11005170 (WB 206366727192 2 0x39bfdc4112c63e8d4fd9e5c5fedf90d617488a6df8c) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6553539 11005170:=(_Q1 band 6553539 8779654 11005170 block0 (_Q1 band 8779655 9336183 11005170 block1 (_Q1 band 9336184 9892712 11005170 block2 (_Q1 band 9892713 10866638 11005170 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤50)
    (hT0:3985≤T) (hT1:T≤4248) (hnu:6553539≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤10347035358042453:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDQ
namespace CYT
open AI AP AN
noncomputable section
def band:Band:=⟨11,51,3913,4221,10696288606516687⟩

private theorem block0:WideCovered band 6684610 8408187:=PRB band Z1.f1792 6684610 8408187 (WB 206366693496 28 0xb2cfadf2556f72360131eecb3eb53515b516d8007c8b2cfad0b85694955ff0c52cb3eb45a959c66d7f7e61b2cfad956562d1f5fce6b6cb3eb6be15824257ef4fab2cfae62955bd235fac11acb3ebaa615624457e6b93b2cfae36e556bfb5f89b7ecb3eb6ced5512057de22cb2cfad30d5535855f675e2cb3eb2481543d857d58c5b2cfabef655051f5f45046cb3eaca1d5384ad7ccf5eb2cfaa55c54dd9f5f22aaacb3ea542952f3ed7c45f7b2cfa830e54c3a75f0050ecb3e9b11952a48d7bbc90b2cfa511054a6055eddf72cb3e8bc4152c8457b3329b2cfa187454aaf55ebb9d6cb3e7b25153db4d7aa9c2b2cf9c79e551cbb5e9943acb3e65e3554b1a47a205bb2cf97d7b54f384de76e9c16be0145c039a427996f4062f8050f00e6885e5490017be008a4014338772ca3) (by decide+kernel)

private theorem block1:WideCovered band 8408188 8900637:=PRB band Z1.f1793 8408188 8900637 (WB 206366693464 18 0x2fbfec96a98809890fa03b7ddf66a52c2e7c48746b6beefb46fb60d43a435ea7df77d9a8cb051fa218cfa2fbbec7dad820a690b55037ddf60836c0ee0085211abeefadfef608d0a424bd9df77d5652b06da42103932fbbe95ae580bd050709cb7ddf38bbec1bd1982fb7eb6dfb1b38587d6641390bdb6fd8a972c237a208b592db7ec3ddd608e6903d1616dbf6114aafd85c81a3fdb6dfb01ba57bf0a40afa4db67d7d1e2bc8462046a5adb3ebc6f15d59d901abc5659f5d296ae66f480912f) (by decide+kernel)

private theorem block2:WideCovered band 8900638 9463438:=PRB band Z1.f1294 8900638 9463438 (WB 206366693400 16 0xc70fbdfb36a91db20cd1d8e1f7aa04d3f5823f749f1c3ef26bda58cc47a9e06387ddecab465428eca59c70fbb08268301f1c81e5861f74470cf26d636de2f0c3ee47459b8d4469712617fdcb013308978ca4bdc2ffba0016573831836ad85ff7296eca002a2e47bf0bfee219192386458444617fdbd5f320ec88a7f21c2ffb6b5f63ae6113eb7585ff6b36ac681a225b14efbfed13a58b53bc471765f7fd95d5313545885984) (by decide+kernel)

private theorem block3:WideCovered band 9463439 10026239:=PRB band Z1.f1294 9463439 10026239 (WB 206366726168 16 0xcf2fa34973c0f2598fcffcf2fa342fbb8202987398cf2fa2e40bb120497ea31cf2fa28243aa1499760cacf2fa21d33a2f9396d763cb2fa1b41b9bc72964dfccb2fa146339476695c495cb1fa0d27b8cffc953b2ecb1fa12eb385b6494b1c7cb1fa0d7fb7feef942860cb1fa07deb7a207939ef9cb1fa01d9b74094931592c71f9faf936cef7928c2bc71f9f45f366d7f9202c4c71f9ed4eb609d291795dc70f9ed7d35a33a90eff5) (by decide+kernel)

private theorem block4:WideCovered band 10026240 11046315:=PRB band Z1.f1794 10026240 11046315 (WB 206366727224 16 0xe70fb998230bd4faa236af9c3edf8f2beb3eaa77adde30fb624daea629a99a03f8bfed1400b69cbea55541e2ffb37f02c5b50a9109cf8bfec990aaea130a32fa5e2ffb0f552b092e288735f8bfebd8faa9f714a10a09deffad929aa0d7ca7fdcef7bfead118a722309ee46ddeffa7481293aa3a77467f7bfe821dea745c89cbed1e2ff87ae92bc91ae6eb00f3cfe91bb67b64d29a9935cf3fa3fce9e94b72683f3b3cbe8e1c6793d3c998666) (by decide+kernel)

private theorem block5:WideCovered band 11046316 11186405:=PRB band Z1.f1294 11046316 11186405 (WB 206366727192 2 0x39c3ef0f0eccb4675561cbce1f749ec63f98aa9a079) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6684610 11186405:=(_Q1 band 6684610 8408187 11186405 block0 (_Q1 band 8408188 8900637 11186405 block1 (_Q1 band 8900638 9463438 11186405 block2 (_Q1 band 9463439 10026239 11186405 block3 (_Q1 band 10026240 11046315 11186405 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤51)
    (hT0:3913≤T) (hT1:T≤4221) (hnu:6684610≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤10696288606516687:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYT
namespace DCZ
open AI AP AN
noncomputable section
def band:Band:=⟨11,52,3844,4195,18367611252260895⟩

private theorem block0:WideCovered band 6815681 8273929:=PRB band Z1.f1795 6815681 8273929 (WB 206366693495 40 0xb2cff3c75544e757f2004d967fa20c2a08cdbf7ea4acb3fcecd94fd555fb6a35659fe6192a7c65efd6fa3b2cff25a053e0017e9515d967f8c2129e651bf392d2cb3fc24254ef075f93e79659fdeef4a75e86fc59c5b2cfee2ec53a6ed7e0a26d967f653629d252bef3b5acb3fab2694ea925f712bd659fd0eb0a77642fb43e7b2cfe573f53dc017d7f37d967f1393aa02e89eae3e2cb3f8a8f94d8c1af4e7015d7fe096aa19d32fa2e09aebfefe5b50c92f7d05a6d75ff7bd6a8638fbe7a246baffbc159430465f38bab5d7fdd0c0a17352f9a319aebfedfcc50b30d7cc02ed75ff6b43a856a9be57686baffb31dd42a2bdf275cd5d7fd82fca14a7af9182aaebfeb57850a32b7c7ab7575ff541c285154be34acabaffa6629429035f15fef5d7fd1254a14f4af88d3baebfe76c450addb7c353fd75ff30f5285b97be11f0ebaff9381543119df04a115d7fc7c50a1acd2f8024caebfe2b6550ee737befc8575ff0c0a287fea9def352baff855d94301e3ef34335d7fc2b22a0ea4977775d49ffc05c500e3e27baa5082c7e02e50071e83dcc79411bf00e60020378ea0c52083f807280100d870aeb1) (by decide+kernel)

private theorem block1:WideCovered band 8273930 8594032:=PRB band Z1.f1294 8273930 8594032 (WB 206366693400 18 0x2db7fe36955e901c191385b6ffc9e32baf8e82dcf9b6dff8da757320b052f036dbff0e60ae09ea09482adb7fe01515b5f0c106495b6ffbc832b553c81c71bb6dff7134567cfd0303476dbfed198ac9e9e04f0b2db7fd7ed158852c07b5a5b67fab402b024380b13db6cff4bf355dd9300d78b659fe8002ab5f2600993acb3fccac95603c3ff06b5967f9594aaa8ce7f9b5fb2cff2d02552140feabcf659fe5ed8a9df69fc41c2cb3fcca7552f1d3f657c5967f9b68aa43847e8581) (by decide+kernel)

private theorem block2:WideCovered band 8594033 9163105:=PRB band Z1.f1796 8594033 9163105 (WB 206366726232 16 0xc2ffe0e0bb1dceda2f45870bff81c1cc6842e8b4672c2ffe0052b17e89a2aee0b0bff7def0c514b28a3093c2ffdedefb10c52a2696930bff78a02c34fce891ab5beffdd4c7309c06a223f1afbff715b8c191a68804d7beffdc0f9304970a1de7a2fbff6ed86c0c0ba86eef9beffdb918b0071fa19902afbff6ce72bf9dca85d91bbeffda3682fe14ca1538b2fbff53bacc1a6ce84c33dbeefd8d1daf499f610e13afbbf5b40ac0cd6083ad5f) (by decide+kernel)

private theorem block3:WideCovered band 9163106 9732177:=PRB band Z1.f1294 9163106 9732177 (WB 206366726168 16 0xcb1fe5b7e375ccf948051cb1fe54f7b6fd3b93f562cb1fe4e2ab69ccd936a73cb1fe4708b63b2f92df84c71fe3f7e35d7f7925495c71fe3775b5729491c9a6c71fe2fdeb523c3913eb7c70fe307034b94c90b3c8c70fe3305b459c89028d9c70fe2c82340b538f9deac70fe259233bc288f12fbc70fe1e1c336bf08e880cc70fe17073333568dfd1dc30fe0e2332e1518d722ec30fe042eb28cbf8ce73fc30fe06d2b2349b8c5c50) (by decide+kernel)

private theorem block4:WideCovered band 9732178 10443518:=PRB band Z1.f1794 9732178 10443518 (WB 206366727224 16 0xe2fff2db12987cf27d6bfb8bffbfff0a74cca9e4520e2ffea453aa4597274bd0b8bff69b56ad5e5d9c1963d33fe9f349e932126c0e173cffa5bd07935aa9a7896cf3fe8e719e06d9a67b69f3cffa167e76fca69962b8cf2fe84a29d76082635f273cbfa08dc75030c984cdacf2fe7b4f1d095625f07af3cbf9d008733db29736fccf2fe6c701c94d725ab0372cbf9922c71657096211ecb2fe5c431c1cb4a5658bf2c7f958f26f8b4c950b40) (by decide+kernel)

private theorem block5:WideCovered band 10443519 11367640:=PRB band Z1.f1294 10443519 11367640 (WB 206366759960 13 0x3ac7f97eb26d8e95ad74d8eb1fe4fb6dad1a0ab1859bac7f8e8026809bfab4b88e71fe24185937922a8d6ab9c3f8439f625846a91fcce70fe0a1d97eb79ea027bb9c3f7e4495d67d6a6f410e30fde90c16dfc7a9778cb8c3f75e835997aca4c854e30fdcd9315dbe3e8ec9db8c3f7200a55e84ba29c98e2ffdbbd3554606e861aeb8bff6acab53f6f5a070dc) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6815681 11367640:=(_Q1 band 6815681 8273929 11367640 block0 (_Q1 band 8273930 8594032 11367640 block1 (_Q1 band 8594033 9163105 11367640 block2 (_Q1 band 9163106 9732177 11367640 block3 (_Q1 band 9732178 10443518 11367640 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤52)
    (hT0:3844≤T) (hT1:T≤4195) (hnu:6815681≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤18367611252260895:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCZ
namespace DBR
open AI AP AN
noncomputable section
def band:Band:=⟨11,53,3777,4168,18931392792254785⟩

private theorem block0:WideCovered band 6946752 8079461:=PRB band Z1.f1797 6946752 8079461 (WB 206367843447 20 0xaeb80e5cd125f3182fb4865aeb80d315123126fefb0229aeb81af9664846da27abbeeaeb817fdfc40cd8967a75b2aeb815e3803bab9127a2f77aeb8121e5331edd0679e93baeb81108ab2f8b02279a300aeb81082222ec9bb6795cc4aeb81051e12f21516791689aeb80e453d2a31aee78d04daeb80ec0322cf5626788a12aeb810470c33ac28e7843d6aeb80f5c5d33a647a77fd9baeb8035dde0ddc955f7b75faeb801069411325b1f72ae8aaa80231c8063d3cd769e71aaa802122a062b5bd7611faaaa8020a97069a22575858305b800066c001c260f4f90c06580002ba0009d6072c730) (by decide+kernel)

private theorem block1:WideCovered band 8079462 8367133:=PRB band Z1.f1798 8079462 8367133 (WB 1306953211991 16 0x5ab600dedfc53b903ffac1d5ab200da64453a3c5ff65e15ab200d539c5391c1ff1fa65ab200d4da8535dc3fed96a5ab200d27a45350b9fe932f58b200cf838534943fe4cf358b200cba98534a37fe06b858b200cad58531aa3fdc07c58b200c4d30532deffd7a415ab200bbf505359b1fd340558b200b7794534573fcedca5ab600a2ad853d257fca78e5ab6007d0e054d11d7c6153d9b2008ca1853924efc1b1756ae053e645daf4847bd4dc56ae03d8d0d62ff147b8ea0) (by decide+kernel)

private theorem block2:WideCovered band 8367134 8708743:=PRB band Z1.f1799 8367134 8708743 (WB 206367742008 18 0x30be03aef8c3d31709c50f75b03e75156c6ae845610b6d81eecaab4bf64207eadb6c0f4c4959a42a0f2666db607907cac42810706bd6db03c9d155f03a833d22b6d81e5dfaadf5c417b73db6c0f389d5631220ac2aedb607adceaa739504d4e16db03db5655029a822434b6d81ec55aa6cdf40eefcdb6c0f3ea1529d72065ef6db6078ddca9128d02a3056db03bd7d546c66810b46b6d81d964aa239d406285db6c0e9b7550785201fb3edb60734b8a808750071296db038c6e53ec647ff258) (by decide+kernel)

private theorem block3:WideCovered band 8708744 9284088:=PRB band Z1.f1800 8708744 9284088 (WB 206367774776 16 0xc708123ce18e24ae36a7e31c2047c5d6321ed8d1d80c3081191158a0b963244270c2044b2a621d498c0492c30811585985d8e62de06f0be04689360c0db8aeba4c2f81178c981eb16297cb70be04492160130989d2b6c2f810cda57fafe62518ff0be04166d5f90a788b9c8c2f80fca917ced4620b5470be03c8395f4a3f87a0dac2f80e26dd7c6e2e1c518f0be0331f45f985f8687ecc2f80b4ba57fe4ee17edd70be024d726065be856efe) (by decide+kernel)

private theorem block4:WideCovered band 9284089 9859432:=PRB band Z1.f1151 9284089 9859432 (WB 206367774744 16 0xcf281535bdbb49ecb38b465940a7730dbda1e5793c72ca052a5d6d23712ab0f5965028b9036214794cc03cb1814773dad2f04a1fc6658c0a34a8d54cd24ecc572c6050ad969ec1d264d3d963027e4ab4ad24929a27cb1813ad35a26e9c906d8638c09b182cfb10e4604e71c604c70367422d21e9858e3025c75b33a2a90684bc708130e41975c247edea63840983b2ca4bea3d3d771c204b2036494e71d85cd8e102512f32119e8e366f) (by decide+kernel)

private theorem block5:WideCovered band 9859433 10614571:=PRB band Z1.f1801 9859433 10614571 (WB 206367775800 16 0xe3081ccc254f93f543ee57c61039b45299885a8378f78c206d18353556c4fe2a7f1840aad3ea965829eac61e2f81888694844bb3b26e7a6702ec189e4f5ea71ea174ce05dc783c1ba04df707699c0b9612772f0c9b6197d33816e4a4ec498d35aa41a6702d4711d50d026922a73ce0595e13a19b84cde19679c0b08c2734db2992fbbcf2815bf04e468c13146899e502bd6b9c485e2605b373ca056cdf3835374bc52b67940ab8e66f8a8c96fddf) (by decide+kernel)

private theorem block6:WideCovered band 10614572 11548875:=PRB band Z1.f1151 10614572 11548875 (WB 206367808536 13 0x77940b3fca72ac6cb038cbef2815c3e0df2ccb5e44a7d65029d9b5b02ae6b82597ac605053cb44b96d6783bf58c09deef6596afabd789eb1812ffaac5113f557d37ce3024b20580558aa696b79c6046b04aed94054465ff38c08c4695b61a0a773d1e70811091ab3819f4cb5c7ce102104f560e24a9507d78c203f54c2b1edf521483f1840796a854f623a31019) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6946752 11548875:=(_Q1 band 6946752 8079461 11548875 block0 (_Q1 band 8079462 8367133 11548875 block1 (_Q1 band 8367134 8708743 11548875 block2 (_Q1 band 8708744 9284088 11548875 block3 (_Q1 band 9284089 9859432 11548875 block4 (_Q1 band 9859433 10614571 11548875 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤53)
    (hT0:3777≤T) (hT1:T≤4168) (hnu:6946752≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤18931392792254785:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBR
namespace DBX
open AI AP AN
noncomputable section
def band:Band:=⟨11,54,3713,4140,47233173434858079⟩

private theorem block0:WideCovered band 7077823 7981123:=PRB band Z1.f1802 7077823 7981123 (WB 206367942775 29 0xaaa726ef0c085a06af79c843aaa726ff3d68133f86f94e34aaa725ceb506be96def8d425aaa7256f65865c1522f85a16aaa724c151859d9c86f7e007aaa724aebb05981a6ef765f8aaa7244a228533b51af6ebe9aaa724905765a58a6ef671daa69721e41cc2574a4af5f7cba69721e3e802571982f5f73da69721e24922559c0ef5f2cda69721dee0a2549b8ef5e9eda69721e518c26125a2f5d82da697222c7662c7ec56f5b4ada69722160e22bbf412f56dada6972200d502b619cef526aea69721ec5182b8fcd2f4dfaea69721d7e602cab736f498afa69721c21262fb20a2f451afaa9721a57a83839f16f40ab0aaa72155442653add6f3c3b0a69720c037a243c45ef37cb1a69721eda952b68b42f35931aaa73f9f84b6f072767335b1a69741d1cce24daefdf31232a69761eb3ec276f71d72eeb23dc82000dfa001bd50f2cb3205582000e04001bd2cf2a7b2041820008b2000fb78706fb6) (by decide+kernel)

private theorem block1:WideCovered band 7981124 8246722:=PRB band Z1.f1803 7981124 8246722 (WB 1306953246871 16 0x5ab60869ff20a2fdb27eeae12d5b0433c5e05183413f662e96ad8219175028c9a89fab766b56c10b9de8147fe44fd1eac5ab608559f40a4a5c67e70d2ad5b0427c14052655d1f2927766c8215554828ae3f7f8cf2db3641086e5c14a127b7c2a8ed9b2083f5bc0a63b097df6c3ac5904347c005024669eec1fd52a71932d79d1f40a0f6e6f0a9539e2ac49072dbf9fb367054a9ceb1ffa7cec9bcbd7cb4aa54e777b583f0ded83eaf18552a7392f0c9cac06d1f4feb4a9538d61f1cfd9c6187a4252) (by decide+kernel)

private theorem block2:WideCovered band 8246723 8496697:=PRB band Z1.f1155 8246723 8496697 (WB 206367774744 16 0xb6d83065f14ac9e40d31cdb6c182f38a50c3e05a4c6db60c0e9a52672d0258556db060277a9244780ef23b6d82feddd48f75c0590e5b6c17e062a4418e01d452db60be3e452044900701b6db05eb31a8f42c7ffb05b6d82f1dd5473483fdeff5b6c176ffea39865fe03dadb60ba55551b43cfe87df6db05c81028ced07f06e7b6d82e1f154622fbf64f05b6c16fef6a2ebbdfa3362db60b6c81518b52fc9fa36db05afd328c11f7e12c9) (by decide+kernel)

private theorem block3:WideCovered band 8496698 8981024:=PRB band Z1.f1804 8496698 8981024 (WB 206367774808 17 0x617c18d4a0b7c618890a20bef831313d6df5611120237df0621ea2d8a83220580afbe0c37c25af0b443cdf9df7c1872aab510d88721e4bef83091c569f7e90d4fab7df061254ad0cf0218b71afbe0c293e59ab6042d9dbdf7c17b90ab442688539a8bef82e82a568d8f9097f357dd05d3bcac7a3fe11162efbe0b57d9591197c1e5be5f7c160ad4b4062683516dbef82b269169e2b305aebd6db06093ca99e1d209753edb60c15f95306924110245b6c1828fca5d79c81e340) (by decide+kernel)

private theorem block4:WideCovered band 8981025 9480974:=PRB band Z1.f1155 8981025 9480974 (WB 206367774744 16 0xc718348e998b461c85587638c1a5896c48e1240c4031c20d1efb61c4a71f6de38e106883ab0a0c38f3ce2c708340b61837fd476169e38419e48ac0b38e3923131c20ce25c5ff8671b9d6b8610667602fb6958d54a6c30832ff417b732c66d4be1841986d8bced423182270c20cd0285dda7d17ccf5861066592aec3598b6c6bc2f832ec197482ac5792e617c195290b973fa29e1370be0c97b15c7d9f13fc7d85f0640b82e0bb489842f) (by decide+kernel)

private theorem block5:WideCovered band 9480975 10105913:=PRB band Z1.f1805 9480975 10105913 (WB 206367775832 16 0xdb3838a2410c31249a3439db383434c5109e3c99401bdb38326e810d7e32984bfddb3833d7c51039d59757dfcf28368ce0d4b2489663c1cb283651b0d3782c95e9b2cb28360bd4d1f098956fa3cb2835dad4d0acac94f594cb28360ce8cf11b8947b85cb1835e35ccdce24940177cb1835b1a0ccd43c938768cb183576b0cb9820930d59cb18354030ca9c4892934ac71834ff04c9570492193bc71834b9b4c809e8919f2cc7183477acc7028891251d) (by decide+kernel)

private theorem block6:WideCovered band 10105914 11105813:=PRB band Z1.f1155 10105914 11105813 (WB 206367808536 16 0xe748324256a927f552ec2bce906391914b9c1ea207df8d20c530c289f7c53c6ecf1a41865464f9887a699bce34830b6129bf8cf4b4b3dc690608d35322d2a92c6038d20bf76fa5a954d1deb16fa417b7244a1eada2c945df482ef49c91d9a143aa4fbe905e2cf51eec6a8384277d20babeea355bdcff675ef9c1726a645e50a9ef8cedf382dddc48a5e973c0961b6705ab155123f4674424b6ce0b2ae1a2035cce0e3a6d9c166338431bd29b2857) (by decide+kernel)

private theorem block7:WideCovered band 11105814 11730110:=PRB band Z1.f1155 11105814 11730110 (WB 206367808536 10 0x3bd20e06273725f4d97e5f77a41bc7f56b703cb20b21ef4836ccb8d0be51622e07d6906c18e9958ed6c08b97ace0d5065b12101579763f59c1a6b055f77d4ae3aaaeb38343f58ba64955a8d19ce906751996be1eeb149bb9d20cc4392c634655af2873a419622756760faa6a33) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7077823 11730110:=(_Q1 band 7077823 7981123 11730110 block0 (_Q1 band 7981124 8246722 11730110 block1 (_Q1 band 8246723 8496697 11730110 block2 (_Q1 band 8496698 8981024 11730110 block3 (_Q1 band 8981025 9480974 11730110 block4 (_Q1 band 9480975 10105913 11730110 block5 (_Q1 band 10105914 11105813 11730110 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤54)
    (hT0:3713≤T) (hT1:T≤4140) (hnu:7077823≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤47233173434858079:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBX
namespace DAT
open AI AP AN
noncomputable section
def band:Band:=⟨11,55,3750,4112,31300588805895278⟩

private theorem block0:WideCovered band 7208894 8044797:=PRB band Z1.f1806 7208894 8044797 (WB 206367876215 25 0x1659082507b09e703bfac0fdaeb84b87db2105c1f7d4e8dd75c254c148f3a05dbe9e4e6bae127ba6473a918df4aaaf5d70a967fd79db35f7a0d94aeb85381ec3a1c4fbbce2e8575c2759e8d63831fde5f836bae13c2cc4b921e76f26c935d70a1574b68dd6f378ee86aeb84e6252ae8a473bc5361575c2384ab0bcd4afbe17bfebae1226756798dca5f02e775d7091804442d01f2f7cf78aeb842e42f8c706833bc3da575c213b8646ce19d9dcffc6aaa08426b20c6b4e3edf05b555041f962061ffc9f668a6aaa820fac98339c42faec8fd554106854c16813b7d52662aaa0831cec0b82b6bea03ab555041651805c512df4ba11aaa8209a4183184aafa39270334200179800701b5d0aa281861000bd00038021e7360608308005f5001bf64727bf5) (by decide+kernel)

private theorem block1:WideCovered band 8044798 8274440:=PRB band Z1.f1807 8044798 8274440 (WB 206367876183 16 0xb6d841561f051f1207e4208b6d84140610520f167dfa45aeb8489d889868a73fdb281aeb846e59b93a9f87fd6abeaeb845aad010464affd22faaeb844c7170dd56b5fcdb37aeb84414a78bedd67fc9373aeb8548ef73cf6cad7c4bb0aeb84ca30fa6a219f7c03ecb2c841613d84f5ac4fbbc29b2c84159b904f55ecfb9847b2c84151b904f6756fb7465b2c841486604f66eefb5084b2c8413de104f0fba7b2ca2b2c84138da04f10b27b08c0b2c8412f4a84f2ed67ae4de) (by decide+kernel)

private theorem block2:WideCovered band 8274441 8568384:=PRB band Z1.f1808 8274441 8568384 (WB 1306953111608 16 0x5cb6169c9ca8d0ff057c80b96c2cf9d551136e09d9f572d859727aa1100c1175cad5b0b2b1b54004181e6f65ab6164ed4a7bfb7033e64b56c2c8c414f04a6055dbd6ad858eeba9d242c087d5ad5b0b1757538ae180c7e85ab6162f26a6aecf010048b56c2c67414c790600e1856ad858832a9850ebff84ead5b0b01e75300897fa8da5ab615d0e8a61a6efec22cb56c2ab8694d70ddfc654f6ed84cdb12aae37bf68c7ad5b0ad1cb5250e67e89cc) (by decide+kernel)

private theorem block3:WideCovered band 8568385 8972557:=PRB band Z1.f1809 8568385 8972557 (WB 1305879369816 17 0x31c215b202c09fc888e90d638428b5ed86102910b30cc7084f890305e4ae1f27ff86109452762bc61439d3c30be16030cbca86d86aaf15d742e63bd5a07890c36d4bae85cee0ab21802174e9d75d0ba38d5601ca42c5f1aeba175050ab85248544205d742e83e956699909f8b8bae85cca9aab957212d26575d0b9122554b4842366aaeba1710a4aa48948425125d742dfb1d53f6a907ba9cbae85ba312a6bc220e562d75d0b68fa54b1e441a6e3aeba16b8bea919d0830604) (by decide+kernel)

private theorem block4:WideCovered band 8972558 9560444:=PRB band Z1.f1161 8972558 9560444 (WB 206367774744 16 0xcb1851c20597916c8f0be658c28c1f2cab2824547db2c614500364ce1f2184df9630a1e9b3221339032e8c71850a0198ed6f47d1b0e38c281f4ac64e1e3c4f6b1c61417cb6295131d08a78e10a16e5b0e0a28df4ccc7085073318569146b2a2e3842813fcc201363356fb1c213f44660ad37188c6f8e109ed433030de8bb6b0c7084eebf580851c59394e384272578bfe14a2a5e8b1c2135c7b5fd8631410378e10992f92ff546897894) (by decide+kernel)

private theorem block5:WideCovered band 9560445 10148332:=PRB band Z1.f1161 9560445 10148332 (WB 206367774744 16 0xd3385499d9c95074d6cf6699c2a2f42e2f9726929974ce15084570a3eb3375bda670a7c22b7e48e992b57cf38539e01bbadfcc4de8679c29ab92dc13ce6031273ce14cbf06d23312ef9859e50a6ad83622ba96ed3bcf28531f39ae55fcb2eda6794297282d5c9d25738b73ca14a9de6a32f72a7d4d9650a4bac34a78c94af1fcb2852163da255b4a0fcc659428e454cfae424e40472c61480fc6712a52601159630a3f74b337f1927103) (by decide+kernel)

private theorem block6:WideCovered band 10148333 11030164:=PRB band Z1.f1810 10148333 11030164 (WB 206367775800 16 0xeb185f8c6169aea1509d29d630bce2d2c7668a9cbe1b9c6174c76579d7e53083c738c2dd5e0ad23e0a4f16ae71859a9a157eefd47a4b9ce30b03aa2af53da8acd3b9c6146327575f3b50ca20758c261fa1ba01f3a07532d7485629b4f578013eac49ae90ac2859e693527b1a775d21574cd3c51084f1b8b6ba42ac852779e349da78fd748554c1ced30e53a3011a690aa0a69d63f7a7222074d2152e983a3ecb4dfc7d699c2a54ee733fa29b6973) (by decide+kernel)

private theorem block7:WideCovered band 11030165 11911345:=PRB band Z1.f1161 11030165 11911345 (WB 206367809560 12 0xf34857ddd282b058b5c0b1f33856dd707dfd6ab4a42ef338561e2278db94b38520f33855415874d1d9b26612f3385468e270f444b14704ef38537d846cc99ab027f6ef385307dc690460af08e8ef2852645666479aade9daef2851bfbc63a739accacceb28511680611dddababbeeb2850635e5ea4cdaa8cb0eb1850577a5c5c92a96da2) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7208894 11911345:=(_Q1 band 7208894 8044797 11911345 block0 (_Q1 band 8044798 8274440 11911345 block1 (_Q1 band 8274441 8568384 11911345 block2 (_Q1 band 8568385 8972557 11911345 block3 (_Q1 band 8972558 9560444 11911345 block4 (_Q1 band 9560445 10148332 11911345 block5 (_Q1 band 10148333 11030164 11911345 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤55)
    (hT0:3750≤T) (hT1:T≤4112) (hnu:7208894≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤31300588805895278:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAT
namespace CZE
open AI AP AN
noncomputable section
def band:Band:=⟨11,56,3750,4084,30760068026545820⟩

private theorem block0:WideCovered band 7339965 8026962:=PRB band Z1.f1811 7339965 8026962 (WB 206367876215 24 0xaeb86a20131fcc58f7d3da9575c34a5f64ebcef1be8cb2abae1c13880d140d0ef3d4875d70df1b6e6526d5779a1bbaeb87001bf34e6c59bcac9a575c36772615cd19cde442b2bae1bbd274cee8506f1904b5d70db365d614de27787f9daeb866982398a252d7c1b8b575c34785b91d3370bdfba3abae18a14942c4120cef4c0f5d70c43ff41423752775d7faeb861f7988a631eb3b9c9e575c311cb2c9540a39dc53e2aaa083cca00c70f2bed98e1555041cf90062fe0df63b61aaa820db1483256a4fad5295554105d93416dbb07d4650eaaa082a7ae0b6c9f3e9a1795550412eb3060fbf5f48834aaa820685d033a4b8fa1fd682bc30015ec00700a5cfdc9416a18006c8001fb69e6cc2c0bd0c002560009c847243f8) (by decide+kernel)

private theorem block1:WideCovered band 8026963 8231204:=PRB band Z1.f1812 8026963 8231204 (WB 1306953213047 16 0x56ae1ba779cb3eb6ebf664915ab86bceb624940eafd509d56ae1a723707a2d19bf420555ab8684b111a1e11efcbf8e56ae19c5bac5a3a9ebf1dc195ab87ee746655cba67c2e7fd9b218548902925067ef97dd62c8628dbe09eb85d7bc1b458b218a011427b1295ee75c162c862710c09ec6a97b792c58b2189800c27b34d5ed53a162c8624aeb09e27d0fb30a558b2188d480278ccf3ec318562c86224cf09e45b0fae81d58b218834ac27a6ac3eb0f655ab875607e42564287a9f96) (by decide+kernel)

private theorem block2:WideCovered band 8231205 8528283:=PRB band Z1.f1813 8231205 8528283 (WB 1306953111640 16 0x5ab61dd394a8279a82219b5ab61dc7dca7fd8681d9145ab61dbfcaa7c2e281908d5ab61dbe1ca76b3e8148065ab61dab72a7561680ff7e5ab61db0bea6e1e680b6f75ab61d94eea6e286806e6f5ab61d9b8ea669fa8025e85ab61d6ae6a698ba7fdd605ab61d14caa718127f94d95ab61cf742a6e55a7f4c515cba1b9b52a977d27f03cadbb61adcfaaa0d757ebb425ab61d1c36a400287e72bb5ab61cd81aa44ec07e2a335ab61c7dc0a465147de1ac) (by decide+kernel)

private theorem block3:WideCovered band 8528284 8862498:=PRB band Z1.f1814 8528284 8862498 (WB 206367742008 17 0x18e10d0067628525873b22bae87a718ab8608435509dd743d185d5b695a198632eba1e99dead1abd0c320975d0f504856591c85d07dbae87acc8ab02f142c3fadd743d7b5d57361214fdbaeba1eb1b8ab3ec109edcd75d0f51ac5576fe84ae5fbae87a525aaabb44232ebdd743d05f9548c52107542eba1e71b0aa09cd07a99175d0f2e7a54cfec838c41bae879205aa59b441a1dcdd743c61f15262c20beccaeb61e14f6a8c5fd05655575b0efbc9544ac0826a23) (by decide+kernel)

private theorem block4:WideCovered band 8862499 9456658:=PRB band Z1.f1815 8862499 9456658 (WB 206367742008 16 0xcb187f6a432399ec82609638c3f65a58f61fe3eec0f1c61f8530c673331e53e98e30fb9ca62dbfb8e98e5c7187e4a3311afbc703eb63843f3e7186899635db1f1c21f7be4c27d2f19cb718e10fa99060df6b8c54a9c7087c8b6304307c5e1cd63843ddaf5820b262cca2f1c21ea2cec090571542f98e10f1f266023318a106dc70876b1c301199c4bfaf63843a1d4d81affe23b93f1c21bc500c31e0310ba818e10d6d01615b7e87cc31) (by decide+kernel)

private theorem block5:WideCovered band 9456659 10050817:=PRB band Z1.f1161 9456659 10050817 (WB 206367774744 16 0xd338726f69c0a854cae80e79c391bdededd76632fcb3ce1c7d526e82d73075c79e70e35d1b6c87197a9d4cf2871d4ddb25de4b8c62e79438da84d7a3aa5a1edb3ca1c5f726b152f2bed4f9e50e295bb541db956598cf28710cfda7109ca6a44e594386534d2014a510deb2ca1c207d6837f92764d99650e0ef8b3b41893215dcb1870a5719a844494827658c383b0ccc6d4647fcff2c61c0ee565a17322dc619630dff78b2859c90dd21) (by decide+kernel)

private theorem block6:WideCovered band 10050818 10756382:=PRB band Z1.f1161 10050818 10756382 (WB 206367775768 16 0xe7387889715d5a0a90847b9ce1d68bb5776f5a2ff00eb286f0b757210ae87738b5d61d403c3efe78a0bac4d75874b594f9609280a6d75d61d1af53dbb8c9f98a6d748748084f485fe7c1e5f5d21d10b83c9a169e7688d7487403bcf047e27795e75d21cf0b43b88c29d546ad348737fbcebf7fa730d6f4d21ccffd3a82e69c324cd34872f98ce7eb466e84f74ce1cc78f396b279b102ed33872e60ce3e86269fc7f4ce1caafa38882f99ee10) (by decide+kernel)

private theorem block7:WideCovered band 10756383 11944701:=PRB band Z1.f1161 10756383 11944701 (WB 206367809560 16 0xf74876ed6087bbb9b642fdf34875c56281a642b520dff34874a5887bd396b3fec1f338741d88778623b2dca3f338734444733b27b1ba85ef38726d286f1543b09867ef3871b3026bc098af7649ef387156b468310bae542bef2870b294653dd5ad320deb287025e0630498ac0fefeb286f76da603b77aaedd1eb386f51c65d7d14a9cbb3eb386ee80c5c29f2a8a995eb386e5ea85a6940a78777eb386dc57e58cbe0a66559e7386d32285847d7a5433c) (by decide+kernel)

private theorem block8:WideCovered band 11944702 12092580:=PRB band Z1.f1161 11944702 12092580 (WB 206367809560 2 0xf75878f828941d09b884a4f74877fd268d50dbb7651b) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7339965 12092580:=(_Q1 band 7339965 8026962 12092580 block0 (_Q1 band 8026963 8231204 12092580 block1 (_Q1 band 8231205 8528283 12092580 block2 (_Q1 band 8528284 8862498 12092580 block3 (_Q1 band 8862499 9456658 12092580 block4 (_Q1 band 9456659 10050817 12092580 block5 (_Q1 band 10050818 10756382 12092580 block6 (_Q1 band 10756383 11944701 12092580 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤56)
    (hT0:3750≤T) (hT1:T≤4084) (hnu:7339965≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤30760068026545820:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZE
namespace DDG
open AI AP AN
noncomputable section
def band:Band:=⟨11,57,3750,4055,31518451869895687⟩

private theorem block0:WideCovered band 7471036 8052704:=PRB band Z1.f1816 7471036 8052704 (WB 206367843447 25 0xaeb89599d75596426fadfe0aeb894e8e846de0aefabb3aaeb89146004db9362fa9694aeb8914bbe3bd6f9afa4d49aeb8904eb23906d2afa03fdaeb89c77a664e39af79bab2aeb89d0a44688375f797166aeb897692855dd2e779281baeb89a97aa63e1d9b78decfaeb897f4645ccd17b789584aeb88beadd301029ef84c38aeb88f9e2c42d2c2af802edaeb884b943160175e77b9a1aeb8850fdb1b965aa777056aaa821c47006390a1f7270aaaa821b0510624fa1f69473aaa821b0110678b19f601dcaaa8216add05a8c85f56f45aaa821535f059b71df525faaaa821404005c9a11f4dcaeaaa821152305e0731f49363aaa820d50f06931c5f44a170598800500001c0317400cc06388004f7001c020f3b78004f8800504001bfb07324e9) (by decide+kernel)

private theorem block1:WideCovered band 8052705 8240339:=PRB band Z1.f1817 8052705 8240339 (WB 206367843447 16 0xaeb86f136932a6dd2fdbcd3aeb86be194282c312fd7387aeb869c1392138e56fd2a3caeb86823ec1bf491afce0f0b6d88177dd0a31cda7c97a5b6d88190ae0a20b1dfc72ffb6d881caf70a052ed7c4e59b6d88166a80a1d0817c29b4aeb89513a54b31bdcfc050eaeb89149cf3e2e1e4fbe068aeb88e8ca134cd0f0fbbbc2aeb88c71e32d9e460fb971daeb88c0e182839e1cfb7277aeb88b55cb25ec1c0fb4dd1aeb88ab3ea23e7d10fb292baeb89e12b274d35ec7b0486) (by decide+kernel)

private theorem block2:WideCovered band 8240340 8540555:=PRB band Z1.f1818 8240340 8540555 (WB 206367843448 16 0xbae882affa0a812e24128c5dd74414f9b853ed3d20820feeba20a304c29f10b9037de975d104eb1414f97a48175a8bae882594d0a7af7240962edd74411f60853d0392038c46eba208b0fc29e947901338d75d103fa54150a7d480507abae881d1990a8c432400397dd7440c651054ce8d1fef78eeba20624602a27926fee93175d103255c14ec3d27f2b4caeb82545e81154310bf7100d75c12692e87f40545fa62d6bb21f76d558d02e80fc9ed55d70e85a7c86d1fb07e061e) (by decide+kernel)

private theorem block3:WideCovered band 8540556 8840770:=PRB band Z1.f1171 8540556 8840770 (WB 206367741976 16 0xbee8983582b6a9786e642bee897ecdab4e7b869cf6bae8979d92b31de8653abbae8974672b1496860a5fbae896ed0ab039c85c114bae897083aae67a8577c8bae8973302ac72d852e7dbae897679aaa67284e531bae897a8b2a83f0849be6bae897b082a738684529abae8978ef2a5d2c84094fbae8974b02a4abe83c004bae89700aaa38ae8376b9bae896ae9aa26fe832d6dbae8965aaaa239382e422bae895f43aa13bf829ad6) (by decide+kernel)

private theorem block4:WideCovered band 8840771 9422437:=PRB band Z1.f1819 8840771 9422437 (WB 206367742040 17 0x32c626fd68c6cdb48fc665cb189b62eb1899a23ccf3b1c626a892c504388ea137c71899b8430f6522383a831c62658dcc3568c8d7c09c71899d533088e2233a5cf1c6265e3ac1dcd48c56dcc70899f08302e0622f11171c2264a20c0b5508b31aec708981bbb0285522a7c5f1c225a9e8c0a8e08a0c80c708945662fb4c9a25e7a71c224354abfb6c288e752c7088bfd830c9c662152eefbe263abcaec98887c224bef898b0b2b970221de366fbe261cdcadf56c872f8d) (by decide+kernel)

private theorem block5:WideCovered band 9422438 10022868:=PRB band Z1.f1171 9422438 10022868 (WB 206367774744 16 0xd338907889b95a6cc77ea699c4821f4db3d126174f73ce24012d6cb3b72f954d9e711f91435fb4797380fcf388fca71abf9ccb52bc679447eb58d47186584b8b3ca23e98c69994d2b00979e511edceb46eea94edb4cf288f39c1a13feca2d8ee594477c66cf1d764f221b2ca23ae5266ff9f266bdf96511cd83b319c692a358cb288ec2b595726490860e58c475a34c9ce8e45f8ab2c6239ea964558721d72796311c84d31fbf99058fc) (by decide+kernel)

private theorem block6:WideCovered band 10022869 10698354:=PRB band Z1.f1820 10022869 10698354 (WB 206367775832 16 0xeb4894dc25667882a33e72eb4890281d75bfe1a21944db5892f940f9381ca0f416d75892bd40f70d38a0617fd758927848f480989fcee8d758923890f24f909f3c51d7489243a4efad049ea9bad7489218b4ede6ec9e1723d74891dec8ebd08c9d848cd74891a2f4e9b4789cf1f5d348916bf4e7ee7c9c5f5ed348912b38e5c36c9bccc7d34890eec8e3f1889b3a30d33891066ce1ad0c9aa799d33890e6cce02e109a1502d33890b124de739499826b) (by decide+kernel)

private theorem block7:WideCovered band 10698355 11899216:=PRB band Z1.f1171 10698355 11899216 (WB 206367808536 16 0xf748939436ff12516b22a1e691256981eab5fad1b08bcd2247637bb01fed9a37a79a448b28c71cbddb221c6f33890c01cdcd55f61f933de71200f05aaa822bf5dafbce23d5f033a95257591ef7a4479193645be2ad8d0fef488ea5c8c455c358cfc3de911c492d807baead0acfad22366b92f1cc6d50ec2f5a446804b5c7f70a8f857eb488d161cb3e83f4fa655d69119599964803a9ab7f3ad2230ca1ac624352c46775a445cb68594199a463a0) (by decide+kernel)

private theorem block8:WideCovered band 11899217 12273815:=PRB band Z1.f1171 11899217 12273815 (WB 206367809560 5 0xfb589923f6a1938bbb4897fb5897f01c9a8538ba2608fb5896a82493007fb900daf7589570668bf293b7dbacf758947aa084a546b6b67e) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7471036 12273815:=(_Q1 band 7471036 8052704 12273815 block0 (_Q1 band 8052705 8240339 12273815 block1 (_Q1 band 8240340 8540555 12273815 block2 (_Q1 band 8540556 8840770 12273815 block3 (_Q1 band 8840771 9422437 12273815 block4 (_Q1 band 9422438 10022868 12273815 block5 (_Q1 band 10022869 10698354 12273815 block6 (_Q1 band 10698355 11899216 12273815 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤57)
    (hT0:3750≤T) (hT1:T≤4055) (hnu:7471036≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤31518451869895687:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDG
namespace CZP
open AI AP AN
noncomputable section
def band:Band:=⟨11,58,3725,3749,44481302807416666⟩

private theorem block0:WideCovered band 7602107 8052630:=PRB band Z1.f1821 7602107 8052630 (WB 206366662679 23 0x1555cccf4d941237eb7e5aaab988aaad69f67d28215557304a0580f8d79c0edaaae5d526a24525f26333555cb4c1d2e6ef9e28912aab968c027d07c3c097855572bb4f504d07f7839baaae52ccabe3224ede88d4d3ca07f0b063f1d993c69a7940fe160c7d3b3278534f281fc2c18e37664e6a69e503f258311eecc9834d3ca07dcb05f99d991de9a7940f7960b4abb31f1d34f2818b2c15367662baaa9e51792604d8ceca06d553ca2d28c2d511d8189eaa7943e71832ca3ade0bd54f2846a305ab1f57208aaae50b6e64e5dfea4ff1555ca0c20cf0fe7d377a6aab940549b419bfa49ecd55727ed03c8937f449ca) (by decide+kernel)

private theorem block1:WideCovered band 8052631 8474594:=PRB band Z1.f1822 8052631 8474594 (WB 206367746168 16 0xbae8a180c8299b20d029fc575d142dbc0534d9ba0420e2eba2855380a64b0ac060475d745099d414aba848078e3bae8a1092829776590062735d6e2c79e38691e25ffa63ebadc624b27d10d11bfd0f2d75b9d6ae512121027f5a3aaeb7377f09d861cb0fe25215d6e295f735247405fb2b9abadce6d2e81ff7503f1dc8d75b9a92ccd6b5ed07dac3daeb730db0157d2d60fa39d15d6e5bf5823d5d641f23652ba9cb296c4140c6c3dff1fd75395795471dada07b6eeb) (by decide+kernel)

private theorem block2:WideCovered band 8474595 8768134:=PRB band Z1.f1182 8474595 8768134 (WB 206367610904 16 0xbee8bcb3aa92a485ca86bae8bc36aa7f158582dcbae8bbaa2a6bc5853b32bae8bb09aa584584f387bae8ba512a456b84abddbae8b9792a32e5846433bae8b877aa20d9841c89bae8b73daa0ebe83d4debae8b5b729fdd4838d34bae8b3bea9edda83458abae8b11aa9df5182fde0bae8b0d3a9d0c182b635bae8b4bf29c26f826e8bbae8b7bc29b8138226e1bae8b64529b95581df37bae8a90fe9f9ad81978c) (by decide+kernel)

private theorem block3:WideCovered band 8768135 9226790:=PRB band Z1.f1823 8768135 9226790 (WB 206367610968 17 0x31c62f17ac008948cca26c718b994afe9c7230eb4b1c62d452bf93988bab7dc718ac64b00f7b22c70a72c62b143c3b5708a8cd4c708bba62ef202e27f6031c22e4eebdcf22896e2bc708b4ebafcee36237b5efbe2fe5aad46cc884f82bef8bf5a2b3c1d2201f62fbe2fc66ac9a7487c02ebef8bed52b113521de212fbe2fa30abef708730d9bef8be3caae69621ba4befbe2f79eab458086a185bef8bd8a2abc40219676efba2f492aa9cc8861230) (by decide+kernel)

private theorem block4:WideCovered band 9226791 9813870:=PRB band Z1.f1182 9226791 9813870 (WB 206367643672 16 0xcf28b388d9fa7a4adfb7679459a5ecea57e54c06b3ca2cc2966bb2529418b9e516587331153941171cf28b27659621c49c10e659459104c9d7e24bcb232ca2c6ff644bbf24c6e7965162a031d32691d41fcb28b22c58be9d48a265658c58f42c5197e42d5db2c62c6726221a3204c439631628db0dcd48f96cdcb18b0e398554cc783bc658c58370c1eb1239e0931c62bf78609b951bd19f8e315e4d3024f08d597b) (by decide+kernel)

private theorem block5:WideCovered band 9813871 10400950:=PRB band Z1.f1182 9813871 10400950 (WB 206367643672 16 0xd758b63f9d5f3ccf5a5b6ba45b358e8ce1678958b5d22d8aa73846d3b2c1bae916bcf3950569d06b9d748b5a29c6eb74e3bb269a45aad2e1a4aa6fa0434d22d43a6fe60d36b177a691697cb77a789ac967d348b4841b7f4e4d1d09699c5a62cda7be266aafb4ce2d21a6c81993236d3a671688935e1d8988c15d338b3fedac0d3cbfe60679c59da2d47f5e5db5b33ce2cd8e69779d2dbc2f9e7166173454c7964ec3) (by decide+kernel)

private theorem block6:WideCovered band 10400951 11428340:=PRB band Z1.f1824 10400951 11428340 (WB 206367677528 16 0xef68b2398c2dbd65730fa77b4590985ef5a52b50d2fbda2c619ae915a9584945ded161e816dc79cab05f9eb68b04f6b383b454f3a875b457c705817042a3229fada2ba7c2b46f614f53fdd6d15ea855656fca68b55eb58aeb86aa666852b65675ac56f6a5587ce291380fad62b1ac2ac4f8d465eb5d6b1521b159a379a210b1db58abbd879db1c5079046dac55cc03c64332818ad35d62adc59decc313fa6bfaeb15692ced34c89f440b) (by decide+kernel)

private theorem block7:WideCovered band 11428341 12455050:=PRB band Z1.f1182 11428341 12455050 (WB 206367711256 14 0x3fde2c3fed590cf37c1915f6d1601f4a3b7efbcf089fb68af1494d40c65de8f07db457316a49a176eaccdfeda2b6ad5178adf73291deeb159f808582d4b875e5f758ac52b3fc617dbab9e7bac55f811e9e8f6d8e24fdd62adc18ec26336a33d5e6b155e5871d6b3b3fb41f368aa75536dc38596e4c79b4552081a9251ac6f7bfcda2a7864ce83a5613e8dded15301a6450e1af809d) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7602107 12455050:=(_Q1 band 7602107 8052630 12455050 block0 (_Q1 band 8052631 8474594 12455050 block1 (_Q1 band 8474595 8768134 12455050 block2 (_Q1 band 8768135 9226790 12455050 block3 (_Q1 band 9226791 9813870 12455050 block4 (_Q1 band 9813871 10400950 12455050 block5 (_Q1 band 10400951 11428340 12455050 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤58)
    (hT0:3725≤T) (hT1:T≤3749) (hnu:7602107≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤44481302807416666:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZP
namespace CZH
open AI AP AN
noncomputable section
def band:Band:=⟨11,58,3750,4025,31563107902589997⟩

private theorem block0:WideCovered band 7602107 8038175:=PRB band Z1.f1825 7602107 8038175 (WB 206367843447 21 0xaeb8b1ee0b4386f59faa71faeb8b0816a3ea5711fa8217aeb8b0ada33fdec6dfa5d0faeb8bea87976b64727a1300aeb8bd536c72fa57e79c8f0aeb8b694a859df8a2797ee1aeb8b7ff3661490667934d1aeb8b4693454b017678eac2aeb8b9682f6c9fe0278a0b2aeb8ac320f3635381f856a3aeb8abd65037b2e69f80c93aeb8a4b413180148177c284aeb8a43af6190a719777874aaa86131b10947a4cf72e65aaa82192f8063b2a076e455aaa821825d0639204765036aaa82170d9065ee9075bc17aaa82131c70598c347527f8aaa82120af05c83a474dde9aaa820f9dc05e1b907493d9aaa820bf94069e6687449ca) (by decide+kernel)

private theorem block1:WideCovered band 8038176 8189850:=PRB band Z1.f1826 8038176 8189850 (WB 206367843415 16 0xb6d8a166590a0ecfff9ef355d70ce3c6c3651a65f34a4ebae19a416464aa86be56c5d75c33075d8bac7377c8884aeb866017615e3d7af8c6f95d7177ce8eda5beebf0f9d2bae2d62369536b1f7e0cb6575c58a6b1225a9f0fbf465aeb8ae5a53397c8ddf79ebb5d7158578a626e293eea956bae2a995a0a9f5d27dc2a6d75c5544b31385bd8fb6046aeb8a9ebdd24dd345f6767d5d7152c1f245e585bec58dabae2da79b989bee53d7897575c5864aa25546067acc27) (by decide+kernel)

private theorem block2:WideCovered band 8189851 8436323:=PRB band Z1.f1827 8189851 8436323 (WB 206367876216 16 0xbae8a0f289853c458602e98eeba28369fe14c6cb0807054bae8a0c265853697e2009912cb208d9ae2310f7b47fdc35b2c823080c0af66bd1fe4896bae08ae34e277ef847f4816aeb82277b288fb4251fbf81abae088fba420d18947eb3f7b2c87044c3bbe187adf9a79ebae1a92430982b8137e1fd8b6d8a0eab9050c3489f75722db62837d8e14238917db0c1b6d8a0d302850a7bc5f62ee6db62834ee214082d07d66b1b6d8a0c9518503f361f506a6db6282f17a141a1b07d1ca2) (by decide+kernel)

private theorem block3:WideCovered band 8436324 8739675:=PRB band Z1.f1828 8436324 8739675 (WB 206367742040 16 0xbae8b4044aac10ea156d6eeba2ce53eaaba8685114cbae8b3453aa9cb7a131cf2eba2ccec8aa2dea847d2dbae8b33522a791aa10cc76eba2cdebea94f8a83e90ebae8b373e2a42f7a0e7bfaeba2cd9c2a8cd4a8354efbae8b35032a2590a0c2b7eeba2cc9d6a86b1682c0d0bae8b2db72a152ca09db02eba2cc378a7bd82822cb1bae8b28efa9f0f6a078a86eba2c7e28a7db5e819892bae8b13c9a9f1116053a0aeba2c1224a72cf4810473) (by decide+kernel)

private theorem block4:WideCovered band 8739676 9118864:=PRB band Z1.f1829 8739676 9118864 (WB 206367742040 16 0xcb18ac6163151a622c92432c62b6b0cc20c038a9071cb18a3f20b23495a27f14b1c22c8898c05f79896833bef8b6407abdd9f2235052fbe2d9e3aaef280888a05bef8b69cf2b9e18220ffd6fbe2d9c22ae266087f5e6bef8b63d6ab6de121eaf5afbe2d8254ad5b248761c7bef8b5d2cab429121c5edefbe2d65f6acbac086cda8bef8b557aab1b1421a0e62fbe2d4454ac1f28863989bee8b4c0faaef77217bdeafba2d1986ab502885a56b) (by decide+kernel)

private theorem block5:WideCovered band 9118865 9725567:=PRB band Z1.f1182 9118865 9725567 (WB 206367741976 16 0xcf28bb3d633cdca94667fcf28bac993370ba93d260cf28ba581332ca6933e41cb28b9d8c32e92292aa22cb28b936432851c921603cb28b90dc323ee69181e4cb28b97b831f7e390edc5cb18b97ba31a46e9059a6cb18b908eb17b8e8fc587cb18b884bb157918f3169cb18b7d69b116488e9d4acb18b715030fc718e092bcb18b61dd30edfc8d750ccb18b4b7db0b9498ce0edcb18b2cd430cd048c4ccecb18afab4b114998bb8af) (by decide+kernel)

private theorem block6:WideCovered band 9725568 10332270:=PRB band Z1.f1182 9725568 10332270 (WB 206367741976 16 0xd748bfe3c3a5b0b9da86ed748bf824b9e66f9d144fd748bf18ab968c09c8030d748beb33b8f95f9bec11d348be488b888af9b57f2d348bdc9e37fcb29ac3d3d348bdc173786f79a2fb4d338bdd31372189999b95d338bd6eab6b2e7990776d338bd113b6596c987358d338bcae335ffbf97df39cf38bc364358b89974b1acf38bbc27b52e8396b6fbcf38bb5c334cfb79622dccf28bbf2bb456b2958ebdcf28bb9b4b411c594fa9e) (by decide+kernel)

private theorem block7:WideCovered band 10332271 11166487:=PRB band Z1.f1830 10332271 11166487 (WB 206367775800 16 0xef58b8860177c0e154c62fdeb16efc1ae2805aa4eb67bd62da0d25bf28554094df5ac5a756cb6800aa6ea5def58b24e316ebc914b843fdeb157941afbef9e9267876da2c64614027a451b8d1edb458a9607f067ca2dd84db58b126c4fb075d4492cbb6b16243a1f189a286d51f6d62c3ba53dac025090946dac585a087a2136a08d09d758b07d84f221753ff1d5aeb1608b11e0040a7d932f5d62c01b53b66b94f68566ba457fff275a0ca9e3c8d) (by decide+kernel)

private theorem block8:WideCovered band 11166488 12379893:=PRB band Z1.f1182 11166488 12379893 (WB 206367809560 16 0xff68b79eb0a935d8bce6f5fb68b641a2a048d1bbbeb7fb68b4d05c96d73cba9679fb58b3f2bc8f6da3b96e3bfb58b304f4898d6bb845fdf758b1fff0831993b71dbff758b1616e7d7607b5f581f748b0ac56792565b4cd43f348afec46749f25b3a506f348af47867104bfb27cc8f348aee6506cd1a6b1548af358ae556069a440b02c4cf358adda386745d0af040eef58ad41886451d9addbd0ef68ac9c386166bfacb392ef58acb9fa5fc069ab8b54) (by decide+kernel)

private theorem block9:WideCovered band 12379894 12455050:=PRB band Z1.f1182 12379894 12455050 (WB 206367809560 1 0xff68b916acb2ecc6be0c8a) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7602107 12455050:=(_Q1 band 7602107 8038175 12455050 block0 (_Q1 band 8038176 8189850 12455050 block1 (_Q1 band 8189851 8436323 12455050 block2 (_Q1 band 8436324 8739675 12455050 block3 (_Q1 band 8739676 9118864 12455050 block4 (_Q1 band 9118865 9725567 12455050 block5 (_Q1 band 9725568 10332270 12455050 block6 (_Q1 band 10332271 11166487 12455050 block7 (_Q1 band 11166488 12379893 12455050 block8 block9)))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤58)
    (hT0:3750≤T) (hT1:T≤4025) (hnu:7602107≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤31563107902589997:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZH
namespace DCO
open AI AP AN
noncomputable section
def band:Band:=⟨11,59,3381,3995,31335780865062296⟩

private theorem block0:WideCovered band 7733178 8088752:=PRB band Z1.f1831 7733178 8088752 (WB 206367909015 16 0xb2c8ce1edad8a906f9f6d961554e1dfcafac0ca465eda00aaa9cc5b21f66f34edfda14c5553991d180d80e2447b1d2faaa731a8461a44afe7f5ef8b554e64544bb66d3d6deab3c6aa9cc3a6726225f517d310f575c545396c6d845a27a174aaeb8cfd0f5d9622073f398ef5d71a0d9353597e267e6068ebae334b7d957c5228fc9b685753e0cf52615d2cf8f8ebfcaaa70f096299473f02f0acab5d6f82d03105e53463df02baaaa0838de305ae7883b9583d554106d1d40b4ef10769560) (by decide+kernel)

private theorem block1:WideCovered band 8088753 8131343:=PRB band Z1.f1563 8088753 8131343 (WB 206367876151 16 0xaeb7c3e01085c7ca5f8261f6591b8f31e622b2bdee21e6cb2371e62ec45652bdc43c59646e3cc0988ac867b8875b2c8dc78793115304f710556591b8e7f5622bac9ee1e52cb2371d27cc47253bdc334d9646e3857d88ae7c7b853eb2c8dc6e6ab122ebef708256591b8cf2f62453e5ee06f2cb23718336c489d43dbfb2d9646e2d0598913717b7d0eb2c8dc59463138b5af6f56f6591b89347626b265edd82acb2371076cc4d0b4bdb8aed9646e1d1358998217b6f07) (by decide+kernel)

private theorem block2:WideCovered band 8131344 8982802:=PRB band Z1.f1564 8131344 8982802 (WB 206366860344 16 0xbaef99eb87a50c996891112badf949c0a1d895de88867cb6df9102af187357e87fbe7b6df8e662994c3f5e877151b6df8c680811f569886e6bcbadfa061062f43914865c26badf93e9159d6c58c8546fbb6df8ef93196851988431d0b6df8becc1926ecd2831ca6b6cf8ac1f9100728482077bb6cf89f4eb8f2870680f250b6cf89a1098f30b1c7fdd25b6cf48f22d0f06b637ec7faaebf841838063db347db2cfaebf841d69060cc0e7d283aaebf83fe4685e8e7c7c9da4) (by decide+kernel)

private theorem block3:WideCovered band 8982803 9550441:=PRB band Z1.f1832 8982803 9550441 (WB 206367908984 16 0xcb28c1c2e2c2db57c92374d396518383f185adcf5244bf4f2ca307064d0b490da48529f659460df384167ed74901aa8cb18c1b7d942cca1191f20279631835b95859428723c15f72c63068c4b0b266e2473d74658c60ca660163d95c8df052cb18c188ea02c631b91acb7b963182f48285905992336c9f2c6305ab560b236fe462849658c60a98e6165da048bc5fdcb18c146b982c492971676d175cf1f84982cb61f2a2ac34aeb9ec145df5cd2f9cc5131edd73e8a493ec530988899ba7) (by decide+kernel)

private theorem block4:WideCovered band 9550442 10118079:=PRB band Z1.f1182 9550442 10118079 (WB 206367807512 16 0xd348d091acc94546698eff4d2342507b1f77899d929d338d06e78c6724a653a534ce340e7f31474098c3ffd338d0092ec412fa60e5ab4ce33f3a5b0ae0a97aed4cf38cf8fcac156fa5c90ff3ce33d89cb012519699a9cf38cf6516bed902583c533ce33db25af568195847ecf28cf4f88bc769653e7a73ca33c6442eda33946f54cf28cede1aba598a4f92ff3ca33a9342e68bb935a29cf28ce5d76b892fe4b3e532ca338b57addf7a9244fe) (by decide+kernel)

private theorem block5:WideCovered band 10118080 10863105:=PRB band Z1.f1755 10118080 10863105 (WB 206367808568 16 0xeb68d6cbc89612c2a5c201eb68d595b4959860a4acd6eb68d3d48e968caea397abeb68d0415c97f85aa28280eb68cbc7fe98f73ba16d55db58d278466e03f4a0582ad758d239fc6d09ae9fcd95d758d1f97a6c0c2c9f42ffd758d1c3886b35ea9eb86ad758d1ca046a304e9e2dd4d748d1ae16694b029da33fd748d17e7e68a18c9d18aad748d146e667d2a09c8e15d748d10cfe6701489c037fd348d0d7366655f49b78ead348d09778657ed29aee54) (by decide+kernel)

private theorem block6:WideCovered band 10863106 11998383:=PRB band Z1.f1182 10863106 11998383 (WB 206367841304 16 0xf788d3548c70b15db714aff788d27b206c5a02b5ff84f388d1bece68bab2b4ea59f388d104be653cbeb3d52ef388d0920461797ab2c003f388d0035b5edf8cb1aad8f388cf74e25c5ea3b095adef78cece26596cccaf8082ef78ce992a570552ae6b58ef78ce310d553b80ad562def78cdac56531810ac4102eb78cd34b65178b8ab2bd7eb78ccb3184fed73aa16aceb78ccbbe34de8dda90181eb68cc5d8b4cf499a7ec56eb68cbf6334c2e7ea6d72b) (by decide+kernel)

private theorem block7:WideCovered band 11998384 12636285:=PRB band Z1.f1833 11998384 12636285 (WB 240727581752 9 0x8b6c6d1b4ca60c7f3c0d07d7fc46e85279511964bfbe057fbc6dc40593de7d2bea8da7fbc6cf77e12cbc18bd93af7dbc6c24e091b0b68bc7e847db46b99f790c90e2bb695a7dbc6b0e849011eb2ba542f7bc46a7a730f4f4e6b93f047bc469fb030eac124b829d9) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7733178 12636285:=(_Q1 band 7733178 8088752 12636285 block0 (_Q1 band 8088753 8131343 12636285 block1 (_Q1 band 8131344 8982802 12636285 block2 (_Q1 band 8982803 9550441 12636285 block3 (_Q1 band 9550442 10118079 12636285 block4 (_Q1 band 10118080 10863105 12636285 block5 (_Q1 band 10863106 11998383 12636285 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤59)
    (hT0:3381≤T) (hT1:T≤3995) (hnu:7733178≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤31335780865062296:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCO
namespace CZZ
open AI AP AN
noncomputable section
def band:Band:=⟨11,60,3328,3964,34167255524904513⟩

private theorem block0:WideCovered band 7864249 8040831:=PRB band Z1.f1834 7864249 8040831 (WB 206367908919 16 0xaeb8aaa81a0f919b47ab17faeb8aa8f5a0f6f7267aacc6aeb8aa66da4f363e17aa80caeb8aa3f848efeb2b7aa353aeb8aa28574edec387a9e99aeb8aa11624ebf21e7a99e0aeb8a9f63ace9955d7a9526aeb8a98d67ce17d737a8240aeb8a9c2d80e8c5e97a5c74aeb8d245039b932cafa10ddaeb8d00fe11c567aff9c545aeb8ce0d2a55e3338f979aeaeb8cf9e8058da0bbf92e16aeb8cd903e162b388f8e27faeb8a6d1144b85e607896e7aeb8a66edd4b66cb7784b50) (by decide+kernel)

private theorem block1:WideCovered band 8040832 8086791:=PRB band Z1.f1835 8040832 8086791 (WB 206367876183 16 0xaeb8ac4cc911a92b0fb6507aeb8abeb2b91239c0fb5221b2c8fceeefb154e197b3f3bb2c8fcf6b131a0f1f7b35c8aeb8ab3816902f1e6fb2c55aeb8aae2170fb9b06fb196faeb8aab7ed8f801d6fb0ffcaeb8bfc48eb5da8247b0689aeb8bd36d6b1c8afa7afd16aeb8ba8a60ad795cc7af3a3aeb8b8eba62af0b167aea31aeb8b6a173a7399847ae0beaeb8b57910257285c7ad74baeb8b39c07226ae2e7acdd8aeb8b58f12a0e9f787ac465aeb8b5c72e1fc8e1c7abaf2) (by decide+kernel)

private theorem block2:WideCovered band 8086792 8130332:=PRB band Z1.f1836 8086792 8130332 (WB 206367876151 16 0xb2c8ff3f5f315559ff81e396591fe22396258983f016a6cb23fb9a20c42682fdfe1b59647f6f33d88f2aafbf2c3b2c8feb23530fa77bf7d2a16591fd5b02622ccb7ef7f76cb23fa04a8c3cf41fdeb3559647f2bd7d86b468fbccf7b2c8fe52dfb0f535bf787096591fc4f6d61ae02beee846cb23f89a08c3f707fdd84f59647efe059871524fba72bb2c8fdd39330cbbcff73b716591fba4e261ecc1bee5116bae2b1382c4eabf63dc569575c56017189327ae7b77ed) (by decide+kernel)

private theorem block3:WideCovered band 8130333 8173872:=PRB band Z1.f1837 8130333 8173872 (WB 206367876151 16 0xb6d8ef6149aca0b7bf972616db1dd0a7b5cccc53f2992ecb23c3f26ee9805b3e49b2d96477411a5d253aa7c807fb2c8f901b134137a6f8db336591f712b56665439f1909acb23f7bb4ec98124be2d59d9647eb9c559402e27c5140b2c8ffcbe1b173340f88f9b6591ff783a62c7289f10c52cb23fed9f0c5b516be1f2d59647fd10558adab07c39a1b2c8ffabde3187072f869cf6591feffad62be6cdf0add2cb23fdd272c5ad6a3e1100d9647fa3a798a15087c188f) (by decide+kernel)

private theorem block4:WideCovered band 8173873 8309333:=PRB band Z1.f1838 8173873 8309333 (WB 206367876183 16 0xb6d8faff5eab6286a7eca55b6d8e568d8fc97bb97ea489b6d8f9d04caa919187e7ebdb6d8f977c5aaa69967e58f2b6d8f9230d2ad773c7e3326b6d8f8d249ab2a3bc7e0d5ab6d8f887732baa7907de78eb6d8f7a5f82b45ad07dc1c3b6d8f756e0ac214227d9bf7b6d8f70a8fad55a527d762bb6d8f6c3632f0da627d505faeb86a2e4b8ef0414fd2a94b6d8f20da4294f57a7d04c8b6d8f14295a94da0e7cf1e2b6d8f0b83a2a2cc367cdefcb6d8f019e4ab423207ccc16) (by decide+kernel)

private theorem block5:WideCovered band 8309334 8464144:=PRB band Z1.f1839 8309334 8464144 (WB 206367876216 16 0xbae8ef3c7199d8269a049c42eba3bbe3ca6771e96810145bae8eeb29999eb3d5a036de6db63fcf3f8dcb824d80b5aeb6d8fd8807b58b3196023f8adb63ef2504cfda61d806a16bae8f8cb6bb108ef7201112aeba3da4bb4bb5ed03801e7fbae8f604edb093426dffe2ceeba3c8028aabf691a7fd2e7bae8f0e4fdad053f49feb46eeba3ab4e0087249517f8750bae8e89a00a2e6e5c5fd8612eba395de5e98885617f3bb8bae8e07259ebe96e65fc57b2db638f2c97f52ff787ef021) (by decide+kernel)

private theorem block6:WideCovered band 8464145 8677010:=PRB band Z1.f1840 8464145 8677010 (WB 1306953278584 16 0x5ebe3c0b2ec6a1c410c233492f5f1d9c64dab7c9a22106bed7af8ec42d215791191079ec6bd7c75ce59eaafd1688383cc5ebe3ae22415b0b494419c1a2f5f1d58ee42f43efa20bb27776e8e136d4825cf32905420bbb74709752e12f038c827b3addba38487910982356412ab76edd1c22c7604c49b1208be897af8e4d3dd9d3b26d70413acbd7c7065064d4a011a81e40b5ebe38f4242d2c7cf4c0df1faf5f1dc5038f166a4460661cd72e8e7ca118cd2405102e54eb97473d4f0a665a380814cdc) (by decide+kernel)

private theorem block7:WideCovered band 8677011 8986633:=PRB band Z1.f1841 8677011 8986633 (WB 1306953278584 16 0x60c23863ac909f1f26449004b0611c3116a84f74db22351c98308e1820e027ae2591111b4c18470be14a13d19ac883d4360c2385e17d09e675e43f8d5b0611c2e82c84f24f521e98518308e16f2e0278d9290eb4f8c18470b4baa13c5f4c870ee560c23858aa409e39e24361a6b0611c2b4c104f2dcf219ded98308e14ffac27a7a590c583cc184709f91613ed58b85e087dfbe384e47209e919542ca786fdf1c26ae184eb6ee61525677ef8e11836c27b1c0309fb82bd7c7837018d8c569884b22a) (by decide+kernel)

private theorem block8:WideCovered band 8986634 9373662:=PRB band Z1.f1842 8986634 9373662 (WB 1305879402616 16 0x67947bb680b672764783ef33ca3dae605a451ae39c2bd9e51e7cecadadb851bb301cb28f193e17344c98d425163847d333aa3789c46559131c23e9219519ed62317e2d8611f4679a8b58411827e6c308fa1f1d44db708bc85c61847d0534a2043845be6230c23e7d6e50ccc022cc4b58611f3c2a284b3a115cb2ac308f9cd69417bf08a99fe61847cdd2aa04c00452733b0c23e6a284feb122280b418611f3153a7da5b1136e70c308f93ac93e55c0896ba1) (by decide+kernel)

private theorem block9:WideCovered band 9373663 9992909:=PRB band Z1.f1188 9373663 9992909 (WB 206367807512 16 0xd348f07d62c20fc661eb374ce3c1bb930244097e39ed338f02f76bf6cd25d31bf4ce3bfa9daf926496b540d338efa742bd90965878474ce3bd4a12f1d429586e2cf38ef167abb590253becf3ce3bc1182e8eae945884cf38eef38ab918724f055b3ce3bb69d2e0bb1932a27cf38eeb412b785424a4be33ca3b9e24adad0591fbc9cf28ee0f16b6355645926b3ca3b63752d75bf90cd6bcf28ecf1f2b5a83640d8f33ca3b132aada7348f9f0d) (by decide+kernel)

private theorem block10:WideCovered band 9992910 10612155:=PRB band Z1.f1188 9992910 10612155 (WB 206367807512 16 0xdb68f349f0dd391e87b6ef6da3ccc33b6bb07a1568cdb58f325acd8b5b682fd776d63cbb6d35cdd4a0282edb58f2ac40d5654e7e43ff6d63c9a06b4e3d79ef9d0d758f220a8d1b3da798a875d63c754bb3f4109dcb72d758f1d34ecde21674d1135d23c74c03314cc9c9d15d748f19b90cad14e70179b5d23c572fb2559a9b6eb7d748f11a22c7d89e6b5e234d23c34b7b1958e9a4059d348f08ba4c5127a66a4ab4d23c1f1630ea209911fb) (by decide+kernel)

private theorem block11:WideCovered band 10612156 11579727:=PRB band Z1.f537 10612156 11579727 (WB 206367841336 16 0xf378f050f36006ad5858a7f9bc77eb06aea59dabe0bcbcde3be25e16ba9fd5ca929e6f1de0c46b38952ad2636f378ee5384582d3e55fbec79bc76bf12ab7417aab25efcde3b2426d5e23ed53363be6f1d57788b14124a86cbff378e6a7ea5a7e89d39f30efbc753d7a9daf1da9840137de3a968c4eabc8d4af1abbed1d4b11c740260a4e1a6df68ea35c03973bf52253befb475091d9c732aa8ecd237da3a7c6c4e1b951463833b6d1d398186fbe52a284ea) (by decide+kernel)

private theorem block12:WideCovered band 11579728 12817520:=PRB band Z1.f1188 11579728 12817520 (WB 240727613464 16 0x81c479fb65db7845d8728e10388f25fc2b2d404309a33e06f1e1fe3e5d72b1609d38c0de3bf1e58ae61d1c00c137fbc774bfb14471297dbb6aff78ed9f1aa61daeaf6bd61fed1d9e50347d9ef5e407d3fda3b0ad5087f433bb529c7db475c25b503625974487cfb78eb07a81ec03dee3d785f6f1d4f8bb3ae696dbe3c1bdde3a81c1871a95cb699257bbc74c06ccd9d9bd6ad58ef788e940a69a263eed0f1a5eef1d1d70a32f0cdd98705bdde3a2194e62a576b1dfad) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7864249 12817520:=(_Q1 band 7864249 8040831 12817520 block0 (_Q1 band 8040832 8086791 12817520 block1 (_Q1 band 8086792 8130332 12817520 block2 (_Q1 band 8130333 8173872 12817520 block3 (_Q1 band 8173873 8309333 12817520 block4 (_Q1 band 8309334 8464144 12817520 block5 (_Q1 band 8464145 8677010 12817520 block6 (_Q1 band 8677011 8986633 12817520 block7 (_Q1 band 8986634 9373662 12817520 block8 (_Q1 band 9373663 9992909 12817520 block9 (_Q1 band 9992910 10612155 12817520 block10 (_Q1 band 10612156 11579727 12817520 block11 block12))))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤60)
    (hT0:3328≤T) (hT1:T≤3964) (hnu:7864249≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤34167255524904513:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZZ
namespace DBI
open AI AP AN
noncomputable section
def band:Band:=⟨11,61,3277,3933,33040284130127184⟩

private theorem block0:WideCovered band 7995320 8046632:=PRB band Z1.f1843 7995320 8046632 (WB 206367876119 16 0xaeb8b4c987a11b4edeb20a2bae2db19647f1587fabe9caeb8b65ebb1f38e39eae75ebae2d88acc7ba499fab511aeb8b5eebb1ea49ebeac12ebae2d6eccc7982a87aab85aeb8b55b471dde981ea9b02bae2d459727608d37aa1faaeb8b4fe3a1d626f7ea7e5ebae2d398cc750b36fa9d34aeb8b4ce461d234f9ea6b46bae2d3097c744e90fa99a0aeb8b4bc691d0bcb3ea641ebae2d28c6a74232bfa986eaeb8b2f5da1aae145e9c906bae2cbb1a46c2f717a4c13) (by decide+kernel)

private theorem block1:WideCovered band 8046633 8085727:=PRB band Z1.f1835 8046633 8085727 (WB 206367908951 16 0xb2c90f1771184041dbdb06fd964878d5f2c30b705ed5d4ecb243c1dde617cc9af69b9165921de8b030bc2a37b443caeb8a5e911882423f7d9d58d75c52e87d440251d3ecc496bae296f3691faa4edf64f355d714b48128f940aefb1e0faeb8a5934f47b49c77d8a42575c586ed24da9b6e1ec2be2bae2bf65c86741950f602db5d715c4b9eae564a67af7e1aeb8ad437995d82093d772b575c560dc78a0786b9eb932abae2ad476a4b7a3acf5b67f5d7155065ba345fbe7ad1b3) (by decide+kernel)

private theorem block2:WideCovered band 8085728 8124822:=PRB band Z1.f1578 8085728 8124822 (WB 206367876119 16 0xb2c91fd7abb0690f5efe65acb247f445cc20507fbf00ab2c91fa3f5b05f8fdef99fecb247e85dcc1ff6b7bdcf3b2c91f7522b060fadef4da2cb247d251ec10e56fbc9dcb2c91f484bb06946bef0146cb247c747cc13b31fbb6c6b2c91ef2f13036c6feeb4eecb247bcd1ac188627ba3afb2c91ec95c304cb09ee6892cb247a8320c0e9be7b9098b2c91ea298b06c491ee1c36cb2479e75ac171677b7d81b2c91e7e3eb0959bbedcfdacb24795966c227ee7b6a6a) (by decide+kernel)

private theorem block3:WideCovered band 8124823 8289463:=PRB band Z1.f1579 8124823 8289463 (WB 206367908919 16 0xaeb7e22a8c42f6cdcfe7cb7aeb7e20c3242d6730fde857aeb7e1f4d782c18a0fd53f7aeb7e1fd6682ae1d8fcbf97b2c910356d1842c5a7c2b37b2c910355d1842bcd7c2b2db2c910353ed842ac17c2b1ab2c9103449d8422547c2a81b2c910321998444e27c294fb2c9102d6e9840f927c26edb2c9102bca5845e547c248ab2c91021aa583e2d57c1fc4b2c910179a18369e37c1afeb2c9101c53584d26e7c1638b2c910188bd8575237c0cadb2c910015698447b57c0321) (by decide+kernel)

private theorem block4:WideCovered band 8289464 9144101:=PRB band Z1.f1844 8289464 9144101 (WB 206367908952 16 0xc719019fef427e33fa2e1c96eb9fd36baa6cb42418b3cf5bae7eef0e9138a18422aa256eb9faf2cc73d0f3a88a1435bae7e985024c5a40d225ff5aeb9fa09cbd2a6f8d888eb76bad7e70618892b0d22215c5aeb9fccc53567c7b1987c2b6bad7ec7cc6d09266221a67daeb5fa5d56432e3a44857136bad7e7aa5c4a843c821121deeb5f9af02e2627cb4831fb7bad7e6ddb3ca5494b207dbdeeb5f9ff8fa386e6a880ce37b2b7e25fadc3305b21fe95debadf8904830c370cc7f1117) (by decide+kernel)

private theorem block5:WideCovered band 9144102 9618900:=PRB band Z1.f1845 9144102 9618900 (WB 1305879402616 16 0x679c8e604eb531b04962ea33ce4714bd5a2e30248c5d19e72369042d2a6c1233a28cf391a2fbd691f709108b4e79c8b9738b6cf10483a2a73ce44c1255c566f23f7fd19e5230c092c37ce71e9728cf29173a556441ca8eb73467948ae1e6b3c5fcc7116ab1c646f66450d24623639d58e323732ea857c411a888ac7191b4e1141e6788cfa15638c8d8234a0b0544657f2b1c646ad3b5037e223196d58e3234bd4a80c84118370ac7191a28393f8dd08bd155) (by decide+kernel)

private theorem block6:WideCovered band 9618901 10226642:=PRB band Z1.f541 9618901 10226642 (WB 206367807512 16 0xd75911e1a2c58582702f4b5d2446c363117319b7772d749116db6c2f05a6b8c4b5d2444b85b076979a4eb2d74910e0d0c066fe66e94b4d2442556afd47e9925f2d349108560bdd0aa62464b4d2441dc42f2dc097fd32d3491078e4bb1a4e5da34f4ce4412d8ae8f3d96d473d3391005dab96da659004f4ce43ed282e1f6295abb3d3390f5f38b7e2de545d4f4ce43bfb82db7709482f3d3390ecd32b6659a4fba4f3ce43aa472d5b92935a33) (by decide+kernel)

private theorem block7:WideCovered band 10226643 10834384:=PRB band Z1.f541 10226643 10834384 (WB 206367807512 16 0xdf7914cd54e2f9e69547437de4530e2b82f1aa4bd70df6914a178de5c3690a4437da451866372522a394b0df69141804da77b28c01437da44f506362b6aa26bf0db691388e8d6aec2875e436da44d14e352ceca14330db691341d8d2dc2e82bb476d644cb54b43245a01a71db5912f28ccf5ba67e18476d644ab683366af9ef1b1db59126d60cc2bfe7975475d644884c3298039dc8f1d75911e3cec8eab274d2475d64478fa31c2b29ca031) (by decide+kernel)

private theorem block8:WideCovered band 10834385 12011885:=PRB band Z1.f1846 10834385 12011885 (WB 206367841336 16 0xfb99141e4c6c8a8f5ba4b6fbcc899946344c832d882b7de644916b99327c969efdbef3223e20ec2d426b3cf2df7891154eb5f2b1c5953377bc48853642e6081ac5f6bbce243fa2596938c560a9dde7121ef942afe2b8af2c2ef3890f44b75609bd5701b7f9c487578b2a555aab36abfce2438187d4e41795763dfe7121a6e02a5bcc8aa892ff3890c14a252ed1154b03879c48507be2a6ce3aa0dec3ce24177c0d58e4274e1de1bef21524ee72c888a5e630) (by decide+kernel)

private theorem block9:WideCovered band 12011886 12998755:=PRB band Z1.f1847 12011886 12998755 (WB 240727614520 13 0x11e690e272ea8f2569c6586383cc8aa9f14df28ba62993541e244dbe5e66204bb1026aa0712238fe82ef337185c1d50389104ef715a8232c1b82a81c487ad6eca1f27f6047b5c0de4395d684c0b8a2fd9aadff121ae86123e68b17c7bd6ff990cd4f090fb660bd152b7fcc86135fc816f815df6363ee642e035e3db55faeb0eb1f73215c1371d6df3d7335d8fb990a86b68e15624b8722c) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7995320 12998755:=(_Q1 band 7995320 8046632 12998755 block0 (_Q1 band 8046633 8085727 12998755 block1 (_Q1 band 8085728 8124822 12998755 block2 (_Q1 band 8124823 8289463 12998755 block3 (_Q1 band 8289464 9144101 12998755 block4 (_Q1 band 9144102 9618900 12998755 block5 (_Q1 band 9618901 10226642 12998755 block6 (_Q1 band 10226643 10834384 12998755 block7 (_Q1 band 10834385 12011885 12998755 block8 block9)))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤61)
    (hT0:3277≤T) (hT1:T≤3933) (hnu:7995320≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤33040284130127184:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBI
namespace DDT
open AI AP AN
noncomputable section
def band:Band:=⟨11,62,3228,3901,33967310682341084⟩

private theorem block0:WideCovered band 8126391 8995102:=PRB band Z1.f1848 8126391 8995102 (WB 206366860344 16 0xbaefd28435171ca6689411ebaefcfd12893cdcf888a6dfb6dfcdc085914760a880ca0b6dfcbd35b8eeafec877261baefe6e69db38313886d822badfda020823c051485a3a4badfd4b9d39b46426846f27badfd1333097614a0833aa9badfd3e3341cc4a8e82062bbadf4d5b1d961c27780d1adb2bfc4eacc065a9327f9d30aebfc4a7220610f267f02f1aebfc474fa05e00947e68b2aebfc442fd85b26c87dce73aebfc3fce3056e2487d3434aebfc40fd6054580e7c99f5) (by decide+kernel)

private theorem block1:WideCovered band 8995103 9370227:=PRB band Z1.f1849 8995103 9370227 (WB 206367908920 16 0xcb2921bf7c8286e41c77d39e58c90decdc1429ffe3ab5532c6486ec300a10d371cc06b8e3243716e0505a698e1315c71921b690828131bc6e2fb638c90d985814048ee35e35b1c6486c23d09fbe4b1a576f8e32435bf004fab758cde97c71921a932827d085c648bc638c90d301c13dbd563111631c64868a7909e7a0717ee738e324336a884f44db8baa19c7192196910278c68c5ae7d5d73fa9a68ed4acde22c3f6aeb9fb9962548761a514eb3775cfd7039f9ca552089db5d) (by decide+kernel)

private theorem block2:WideCovered band 9370228 9903300:=PRB band Z1.f1850 9370228 9903300 (WB 206367774808 16 0xd3493fda057366012e3989a6927f4342e1cab25a0a174d24fcc735bedf04af42369a49f50b4b76e80954e07d3493e4ad16c78c9296791a6927a9912d906625066274d24edf185b92a849bfa5e9a49cb570b77d8892e50cd349389fa56c536724959ba6727197dad0c35a46c23b4ce4dd3575b0214c88b27e5949ea73ea37324907c10cb293d037d4612e1205de396527975328b1df23f87472ca4f1931512edc47ca5965949e0dd0a203808f4792) (by decide+kernel)

private theorem block3:WideCovered band 9903301 10535090:=PRB band Z1.f545 9903301 10535090 (WB 206367807512 16 0xdb69335146cf2c928302cb6da4cc954b343faa02673db69331f68cb508a7e30d36d64cc19a326d979ef1f5db5932bcaec810f6795edb6d64c9dd031b0cc9dbd77db59322d20c577fa748ce75d64c74d3b0f13d9c88fad75931ade0c2745e6fbaef5d64c67e0b0489d9b547cd759319bbabf78de6ae8f75d24c5bb62f8e1c9a1ffed7493126bebd52a66616ff5d24c35cbaf1de298eb80d749307368bb33de61450b5d24c060e2e9aa597b703) (by decide+kernel)

private theorem block4:WideCovered band 10535091 11206367:=PRB band Z1.f1585 10535091 11206367 (WB 206367808568 16 0xf789361c6ab6671daafedfe78937290077fb3ea9ca61e38936d00876b364a93022e3893674c6756a4aa895e3e38936550273e8dea7fba4e3793630de72b92ea76165e37935e64a71afaaa6c727e37935944e7089a6a62ce8e37935421a6f6d6ca592a9df7934f0906e61a0a4f86adf7934a7ec6d53daa45e2bdf7934a6ca6c0d02a3c3ecdf69347e0c6b1d62a329addf693439be6a4802a28f6edf6933ea0e694524a1f530df69339fa8686e38a15af1) (by decide+kernel)

private theorem block5:WideCovered band 11206368 12469947:=PRB band Z1.f545 11206368 12469947 (WB 240727580696 16 0x81cc9db1d8232aecef91aedff327375b0853f2bbd123d7fcc9c26239fa3266ef76fdff326eb45a78b0b9baa9417fcc9b25ff9d15c06e5d311f7326a2fbc6f6131b840467dcc9a29a19aa5f1edc2f21f73267666067b013b5d74a7dcc9966e39918bfed28b35ef3263c0dc613ca3b36e4f7bcc98860697c89eec8e745ef326220325c4d97b105537bc4983fa516d65a6bf4359ef125f6fda5a03a1ae9c587bc49763bd964d79eb59f69ef125b6faa5affc6ac335c) (by decide+kernel)

private theorem block6:WideCovered band 12469948 13179990:=PRB band Z1.f1851 12469948 13179990 (WB 240727614552 9 0x244b25f8a205c556cac91c568fac981a857f114de71faaa617327045e13cfdcb4c6b62b83cc9ac5fbcdafbbf31606b60f32672e783176bc4c44d2f83c49911ab0b8241a30c62ca0712615e432a9af30c1e43481c497aeed89e1ba9302beda07125d3c842547da8bf7b38) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8126391 13179990:=(_Q1 band 8126391 8995102 13179990 block0 (_Q1 band 8995103 9370227 13179990 block1 (_Q1 band 9370228 9903300 13179990 block2 (_Q1 band 9903301 10535090 13179990 block3 (_Q1 band 10535091 11206367 13179990 block4 (_Q1 band 11206368 12469947 13179990 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤62)
    (hT0:3228≤T) (hT1:T≤3901) (hnu:8126391≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤33967310682341084:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDT
namespace CZI
open AI AP AN
noncomputable section
def band:Band:=⟨11,63,3180,3869,33197636390103700⟩

private theorem block0:WideCovered band 8257462 8416977:=PRB band Z1.f1852 8257462 8416977 (WB 206367876216 16 0xbae95bdfbaaf43d25201bb46eba5656848b31c44b8047e0bae958e9442e4a5e0e0083baeba55489f2a76ff027ff9fcbae953bfe7aa94f489ff4c2aeba5370ebc852d5197fac19bae94c208fa2e7ffe5fe149eeba524fbd48e9bf097f5e35bae9455e10277e5ca5fcdd0edb6578fdf0a994d187f1052b6d95d8909a9d842e1fba582db657553b8a839d407ec26eb6d95ca36aa99dc0a1fa6df2db656fd208a4f72007e748bb6d95bd0b3a9be5561f93666db656c8bcca620e487e26a7) (by decide+kernel)

private theorem block1:WideCovered band 8416978 8576492:=PRB band Z1.f1853 8416978 8576492 (WB 206367876216 16 0xbef94b3d9415c9ddfe0b77b2fbe52a6bfc586633f82b6fbbef949d3ac168bfc9e0a4026fbe523539a5ccb0e7826918bef951476ab58da93a09089afbe5302046d19e2dd821b35bef945209a3405f89207d10efbe50fc9299ea24d381cd51bef9550426f060ca0e06997eeba5444f7663b3dca817f6ebae950e13b18ffd4aa0561f2eba541f66863510ca81318abae95046e798f88e4a042a62eba57b0732bf5709980e3a7bae95e76b6308ab20202f2d6eba57681eec24b3408095c3) (by decide+kernel)

private theorem block2:WideCovered band 8576493 8895523:=PRB band Z1.f1854 8576493 8895523 (WB 206367909016 16 0xc3095195ee98cf504887bc23c719453d1a39316227876e40c3094850c50c64a4e687205dc3095023c958b74ee586d27ac3094ee225d7cef0a4868496c3094d85b596f31aa38636b3c3094b33f454b1f02285e8cfc3094a84661635ac82859aecc30946506050f7aed1854d08c30943c3b6d2dd519184ff25bef94f658615f355a084b141bef94e9b92155b451084635ebef94e638515b657c084157abef94d9e5ad569737083c797bef94d81ce167290008379b3bef94cb03956d3d5c0832bd0) (by decide+kernel)

private theorem block3:WideCovered band 8895524 9214554:=PRB band Z1.f1855 8895524 9214554 (WB 1306953278584 16 0x62c6506b97f09dafef464d2d3163283524084ec277a3131dd8b1941a2fd8275973d17fd28c58ca0cdcf013aaf7e8bb0b162c650649c809d630745b166b1632830cf884ecb49a2c53a98b194175d342783e4d158e0dc58ca0af09013e29168a7923e3c6504ca370a1775345159ff1e328281c104fae2762775718b19417f2cc268f189131ef0c184a87b756ba0b87389419560c253bf8a865645254479d8b06129cffb0b40019c622973983094cc18c5b52bbc110afd4c184a7a9deccf0f1e0880a07) (by decide+kernel)

private theorem block4:WideCovered band 9214555 9573464:=PRB band Z1.f1856 9214555 9573464 (WB 206367774808 16 0xd34959b5056646bd2428b1a672b237aacc86b645e2472ca57961c50e808486e65e594af0974a17774908ee8cb295dc9154240292082099652baf4aa8328423fcc872ca574977503ab047d29ee594ae6568a022488f575acb295c91013fa1a91e12ed9652b8d22a7e06423aee4f2ca570fa94f9a344736d7e58cae089a9ee9d48e1fcccb195be03d3d44291ba3d18e32b755ea7977a23610171c656dc1b4f0f04469b10e38cad97a49de3b48ce83e) (by decide+kernel)

private theorem block5:WideCovered band 9573465 10211526:=PRB band Z1.f1857 9573465 10211526 (WB 1305879435320 16 0x6baca902ab6003719bd0c66baca8fc545f39879b34ff6baca8f5915e840b9a99396ba4a8e69b5ddd8199fd726ba4a8bf685d64d59961ab6ba4a893f25cf0f398c5e46ba4a862da5c8285982a1d6ba4a82cd55c1ab9978e566ba4a814425bbba596f28f69a4a7f7535b67c59656c869a4a7d39b5b246f95bb0269a4a7a4bc5afaa5951f3b69a4a761df5afc5394837469a4a6f58c5b556193e7ade9a4a61cc45c8ce5934be6e9a4a519535d270a92b01f) (by decide+kernel)

private theorem block6:WideCovered band 10211527 10849587:=PRB band Z1.f545 10211527 10849587 (WB 206367807512 16 0xe37955c956dc1a7a9634cf7de555b2c366de2a4f16cdf79551fe0d7890691569b7de554619b5548da3b9dfdf6954f81ad34abe8c78637da552bc9b46428a28251df69546348cfd61a879a2f7da5504f5b38674a14ac4db6953bffecc5a3282bbf76da54e2a532a52ba01336db695381fac8c7527dddc36d654dd45b1bff99edba9db59532f02c5a63a78ff8b6d654b92db113a59da41bdb59529518c2f7da7421536d6548fb1b068469c6c8d) (by decide+kernel)

private theorem block7:WideCovered band 10849588 11846559:=PRB band Z1.f1858 10849588 11846559 (WB 206367841336 16 0xfba9538f786479985a61cffdcca9599fb0edd02ce3047de654726c57df7f964a909ef32a1f920bad37ab11cf6f79950e1135bb7b757f2b47bcca825a42cea262bab76bde653dd9b1676b0d5aec9bef32998b64ba1952ac3ebff7994b6b8e5a662ed58398f3c4a5f1001da5acaa73e8f8e252ecb70ea8d795267bbc7129704f673f514a89816e3894b693e39504d53fe27f1bca5b0471c54c129d82238de52ce3d4e0849d4d8983c6f29620c46f31b6a628fa) (by decide+kernel)

private theorem block8:WideCovered band 11846560 13122683:=PRB band Z1.f1859 11846560 13122683 (WB 240727614520 16 0x8fe4a015161c6f32be41e3dc2e6566e0ee7d03ff31c13b60f32ae0925383e5c18b9ac1079954b7f8997912cc495d283cca9951c0bb249461af2241ea5465a4056652cb089ada0752a06681281342d81de5303a94f426592b7c02bfb79b81d4a72c14c8dbacd5f4006bfea535f26e432d432f521fdff529957111fdf5ed7821e4ffa94c370f0f2ee8ebad9647fd4a5cfecc74b2045cd0eb3eea52be5de37bdf8ae1a921f75294c2151ac2c996e6576fba94a338b0cea8d6b5fb2d) (by decide+kernel)

private theorem block9:WideCovered band 13122684 13361225:=PRB band Z1.f1860 13122684 13361225 (WB 240727614552 3 0x24d72a0bb185f458f6cbe04991ccad1ea017214b872aae5a4732a29f4c52c0a34c97408) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8257462 13361225:=(_Q1 band 8257462 8416977 13361225 block0 (_Q1 band 8416978 8576492 13361225 block1 (_Q1 band 8576493 8895523 13361225 block2 (_Q1 band 8895524 9214554 13361225 block3 (_Q1 band 9214555 9573464 13361225 block4 (_Q1 band 9573465 10211526 13361225 block5 (_Q1 band 10211527 10849587 13361225 block6 (_Q1 band 10849588 11846559 13361225 block7 (_Q1 band 11846560 13122683 13361225 block8 block9)))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤63)
    (hT0:3180≤T) (hT1:T≤3869) (hnu:8257462≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤33197636390103700:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZI
namespace DAG
open AI AP AN
noncomputable section
def band:Band:=⟨11,64,3126,3835,33315626530704906⟩

private theorem block0:WideCovered band 8388533 8549616:=PRB band Z1.f1861 8388533 8549616 (WB 206367909016 16 0xbef964b2438b5e48698274f0bef9693881d9d701b8824d9dbef966cb0c19705037822649bef9635a499781bf5681fef5bef960d097b3e3d95581d7a1bef968525d3877b89581b04ebae968c8e30c40c9a48188fabae968b1638c4d7fe48161a6bef97693ccf42bd574813a52bae96868c64c5373148112ffbae96fef1c97acab3380ebabbae96f8d9b17ac4d8380c457bae96f1688979eda22809d03bae96e3573d7005c318075b0bae96d42b8d6597760804e5cbae96ccec816b21430802708) (by decide+kernel)

private theorem block1:WideCovered band 8549617 8791241:=PRB band Z1.f1598 8549617 8791241 (WB 206367876184 16 0xc3097b34db2d25f73c31264e184bb5c7454bf639617588b0c25bddb6e83c8ab10b0ef58612d8f39247e85e48538d3c309651e1fa6c32e8427515df7cbfd09755c1d62a126e12fbe5f94b96ab84d950899bb7df2fa2057551d9e283fe36bef96faa5797bd4a2c1d7c75f7cb7b1becbf6a1260e20eefbe5bc5efa60bcb0b06c1cf7df2d98f932a69488833993bef96c584a15637f041891fdf7cb5ec1c4ad325420babb2fbe5ad040e58107d90587317df2d4a4842c295c0829c44) (by decide+kernel)

private theorem block2:WideCovered band 8791242 9113408:=PRB band Z1.f1862 8791242 9113408 (WB 1306953278616 16 0xe3c6585aa6e09baacae2c3d0193196542275041300a8ac09964ca587ea3a487f2f6a29c7c5932967eb05b6bb61998a234a62c65a03b282edbbee22752898b1967cead0bcc3cf88985fb62c659a1bb72979cede24dd518b1966290a4a7ecb7788e8ad62c6596b2352adb411e2268158b196b49811898cab6884b5e62c65a3d46a6abaa4961ff2d98b1962503592fa084487ae0f60c25a2e06430bba28e1d7d9d830970f40fd83ab7228710c060c25c0f6da60457b061b086183096e8545569044e0867371) (by decide+kernel)

private theorem block3:WideCovered band 9113409 9435575:=PRB band Z1.f1863 9113409 9435575 (WB 1306953144440 16 0x64ca5f5ec84f606f23fe6dd93297d58093c6bc48fab1064ca5f45bc4efc2923d71a193297cccd93b84ec8f0dc164ca5f295d4e968523afc6593297c3df13a19c48e707264ca5ef3ae4e6535238872d93297b7a79398f248dd32464ca5ec6914e695b23611f193297ac2f53951cc8d35d564ca5e911c4e6a2f2339cb5932979ce61398eec8c9886e4ca5d36f450b082e312779932978925139a76a8bfb37e2ca5e04944e271a62eb23f8f1977b889367d508b5de8) (by decide+kernel)

private theorem block4:WideCovered band 9435576 9918825:=PRB band Z1.f1864 9435576 9918825 (WB 1305879435384 16 0x6ba4b84b6a5acb7e25d65a5ae92e00f0d6aa3d896bc1a6ba4b7a8d65a94f02587b2dae92dd82856aa23095817cebacb4edda5f122525390b5ae92da95f56a2aeb9446dee9a4b621cf5a6912a4ea63fa692d627c1712ed1930c41679cb7afcb50dc4c249bbc99e52de992d42d12892204b6794b79ee750748c247468d9652de52454137a09182fc6594b78ce6500d08244d1519652de06053f9f4890e5ad6594b775304fc46c2425c199652ddb3213e06f090485f) (by decide+kernel)

private theorem block5:WideCovered band 9918826 10563159:=PRB band Z1.f551 9918826 10563159 (WB 206367807512 16 0xdf697462b8c8e4a284b95f7da5d045631dc55a09108db6973b5cac5d10a7fcee76da5cdd15b10ac19f566adb69736532c27c627ae46f6da5cd68bb030599e1bccdb5973313cbfabc675f9f76d65cb7bbaf9d839ce12fdb5972853abd4332710f836d65c88802f04ad9ba691db5971ce16bae3fa6c250b5d65c67d72e8f5b9a6bf3d759717a7cb91d66673a935d65c54ed2dffcf993155d759712aa6b6e17e62501b5d25c3fb62d70b197f6b8) (by decide+kernel)

private theorem block6:WideCovered band 10563160 11207492:=PRB band Z1.f551 10563160 11207492 (WB 206367807512 16 0xe79978ac5ceadaa6ac0d139e25e1aebba1fbfaa65f5e789780f02e60706a7229b9e25dec0d38e37ea92b57e389774ec4e1120ea238238e25dba8337a43aa7f0b9e38976c340dc73669d4dab8de5dae8f3678b5a6b61ce379766890d7df9a9863378de5d84f5b57705a57b7ee37975bbe0d3d5a29378bf7de5d5a92348bb3a440e1df79751284d020da8e8e4b7de5d41bbb3825ca30643df6974fbdccbecee89a3d37da5d2ba2b293c3a1cba6) (by decide+kernel)

private theorem block7:WideCovered band 11207493 12415617:=PRB band Z1.f1865 11207493 12415617 (WB 240727580760 16 0x81dcbd8c60204920bbd72817fdcbcbf661eb0983bc37e37fdcbc133d9d71a37bafd457fdcbbaf989c129d7b9c2a87fdcbb1d4f9b06643b8880a7fd4baa27c1a42b93b74d6d7dd4ba0c489953b43b612cf7dd4b9d716986d123b4d8327dd4b9914c97fe747b39d947dd4b91e84977ae1bb262f67dd4b8b8501755b0bb128587dd4b81d74171c8e3afedbb7dd4b73d9b1733553aeb31d7dd4b5782397db3a6ad787f7decb2f3069e6c8b1ac3de17decb308bd5eba2d8aba093) (by decide+kernel)

private theorem block8:WideCovered band 12415618 13542460:=PRB band Z1.f1866 12415618 13542460 (WB 240727614584 14 0x24ef2d3d634399ae7b67521e4ada5ad4e1f8843825cd6c8393ccbb9458db7aa1699863cb23e97bebda2d87768f2bdd223fd2f248cf6750bf164de5547fa5a10650d84e4d1c8820d85ccbc72da8e7723d18e8edf0bb97669049a2efa031833460f72e8f879302cb60626919c1ee5ca55225811b80c3979683dcb8afff0a34549184b9f107b9703f7d9339540304896a0772de217223f68405ff3de40ee5b91b1c437a1b8bead1f) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8388533 13542460:=(_Q1 band 8388533 8549616 13542460 block0 (_Q1 band 8549617 8791241 13542460 block1 (_Q1 band 8791242 9113408 13542460 block2 (_Q1 band 9113409 9435575 13542460 block3 (_Q1 band 9435576 9918825 13542460 block4 (_Q1 band 9918826 10563159 13542460 block5 (_Q1 band 10563160 11207492 13542460 block6 (_Q1 band 11207493 12415617 13542460 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤64)
    (hT0:3126≤T) (hT1:T≤3835) (hnu:8388533≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤33315626530704906:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAG
namespace DCN
open AI AP AN
noncomputable section




















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DCN
namespace CZO
open AI AP AN
noncomputable section
def band:Band:=⟨11,65,3081,3742,34751473937064351⟩

private theorem block0:WideCovered band 8519604 8722918:=PRB band Z1.f1867 8519604 8722918 (WB 206367876216 16 0xc3098a219327263f6a14679b0c260b1034529cfc584ca7bc3098091f3d4d98856128b16fbe674eff6ac7336c847b0fbef99c5c802b23edf210ae92fbe66e4f60aea335483dc38bef98e78a097d12eee0e3336fbe631a50c542322a836517bef98be9c414ed846a0cf586fbe62e1d1454998328315acbef98b161c95759f0a0bb7dafbe629805055fefa282c640bef989b8e216088dca0a7a2afbe6238e385b31d028276d5bef991e43cb5249106093c7efbe635cc22d5a99a8822769) (by decide+kernel)

private theorem block1:WideCovered band 8722919 9048221:=PRB band Z1.f1868 8722919 9048221 (WB 206367876248 16 0xcb299e08b97b0c535714213b8e3321c3063473bb6a2704cb1c6641578469dd73d44b8e3638cc6a9774b67889989225bc7198cd7a317c62c9311a5df8e332dc1d15de79b22220e131c6655fb14d66d834441a0c638cc6921e58e0891787e4adc719809736afa7630d0f2a8386131aa61731faba161d175b0c26399a43ee1f282437b356184ce891f17366ef386a6ffc3099b446eadf6a0650caf2986132c877050fb3b461820a70c2640bfb0840674042dc5ee184c6c1d5d0d06630856952) (by decide+kernel)

private theorem block2:WideCovered band 9048222 9373524:=PRB band Z1.f1869 9048222 9373524 (WB 1306953245848 16 0x66ce60c3a6613bc6544783aa3367305f62a09e030623adfa7972982e2b804f23db11cd0fbcb94c16182427b13b88e1912e5ca60a553e13f47ebc6e4d372e530504b709eb9f5a35e8ef9729828e8184e5822b1a559ec994cd84e6944874c08cdb6464c6665e63e9ddbf404645fc326332fc5ee4d1b554230f23593298e470a18ac3d6917da42c994c68fdf0c43e5938b9db664ca62b31de5acc7e945a725b26330f02ba266c11062bfb8193298535ec14494ee3155ee8c994c0c877d6c3e1d08a6009) (by decide+kernel)

private theorem block3:WideCovered band 9373525 9698826:=PRB band Z1.f557 9373525 9698826 (WB 206367774744 16 0xcf399d32514310749ff05679cce8d62a1018e4eba7f3ce673c9e505b9726be679e7339b60280b1b930fc8cf399cb8fd3f51ec9602ee79cce312c9f564a49c3cb3ce67034a4f9a1524430d9e73374fc27ba0c91d21bcf399b39213d3e448c157e79ccd7bf49e59a244cd133ce66afe54f0c0b21c7b19e7334df3a7864f90946dcf399a28f53bccfc82281679cccece09dbbbe3fd65f3ce665ff64ecd631f4c579e7331ebd2777228f56c0) (by decide+kernel)

private theorem block4:WideCovered band 9698827 10308768:=PRB band Z1.f1870 9698827 10308768 (WB 1305879435352 16 0x6db4c898da5e50964ea65036da64489a2ec421272b729b6b32212197378b9381de6db5990b0d2b8ff209b701c6dacc822d05c04fc4d68a2b6d663f543adeabc268c9bdb6b31eb6ad6dbed9332730db598ef9e2b6ddd098f4c16dacc74d125b34d64c2af536d66379232dcdf825edc4db6b31a1c6d6f8c892e3078db598b9cc0b99138967965ebacc58fa45b33cb4aed4775d6622bb6aeb134654eee19e731d6329451bc92939c2cf398ea542a20c34944d76) (by decide+kernel)

private theorem block5:WideCovered band 10308769 10959373:=PRB band Z1.f557 10308769 10959373 (WB 206367807512 16 0xe38994b6bad706269ce8378e265226c352776a69b37e3899485eed2283697f1838de6512193422f0a55d89e37993f76acea54292facb8de64eb0233473aa41fdcdf799352aacb30d28e04177de64bf69b26a24a2e22edf7992ee5ac7ae2a890d5f7de64b8edb17ff9a1a480df6992bda4c450d28416a77da649b6b30b456a066d2df6992217ec1b6567f1fef7da647121b00dca9f2925db699168dabf285e7a293b6da6454182f692b9deb77) (by decide+kernel)

private theorem block6:WideCovered band 10959374 11853956:=PRB band Z1.f1871 10959374 11853956 (WB 206367841368 16 0xffb991ba6c61ac722d38213eea642b0f58018c0b3a2d6fba98f72d05f229a2c994a7eea63ab83d79819cb1277bfba98b6d57616f212bfa737fea61dd34985eee6aeac1ffbd98bf9ea625ac06b5b9cbae662edffcecf6c4accf9beb998b85de3a867d2b0c3139e662d49e8e73930ab91ede7998b252a392fc82abcc5b9e662c85f4e1d0a8aa543fe7898b077037e9a12a6d5a39e262b7098dd50a8a91692e7898ab46036d66d2a1deef8e262a192cd8ff04a7d8e4) (by decide+kernel)

private theorem block7:WideCovered band 11853957 13155166:=PRB band Z1.f557 11853957 13155166 (WB 240727613464 16 0x87e4cc3e33de4d3ab9176bd0bc995d48cb66500f1df6c2179327a2476205fce32001c2f26487c66b470dec5025583e4c8559cd4e846987895107c98f601c26dc2b30a1bea0f931d340a492a74e0a4a6c1f2636c0d48a67efc00b9f81e4c6698710631fb7d9be303c98c4f6e1f118eaf6410e077317635f3ba5715e294b3fee62bfe0871ac88bb14e87fdcc533224daa21b73ae76ffb98a29a39a4c2f2e26635ff731388fc3326965badf03fee625514e63cdaab61e32) (by decide+kernel)

private theorem block8:WideCovered band 13155167 13723695:=PRB band Z1.f1872 13155167 13723695 (WB 240761169016 7 0x94ea624fed86bb5385d1682f92fa63cda78709ccecd02d7094f26328ffa84c201cceefc292fa61d43085ea93cbcdb21592fa65722a8c7374c2cc74679102659fa8ec1d5619cb36ba90fe6403d70ba10258c9f90c) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8519604 13723695:=(_Q1 band 8519604 8722918 13723695 block0 (_Q1 band 8722919 9048221 13723695 block1 (_Q1 band 9048222 9373524 13723695 block2 (_Q1 band 9373525 9698826 13723695 block3 (_Q1 band 9698827 10308768 13723695 block4 (_Q1 band 10308769 10959373 13723695 block5 (_Q1 band 10959374 11853956 13723695 block6 (_Q1 band 11853957 13155166 13723695 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤65)
    (hT0:3081≤T) (hT1:T≤3742) (hnu:8519604≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤34751473937064351:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZO
namespace DCW
open AI AP AN
noncomputable section
def band:Band:=⟨11,66,3003,3315,33234960734882178⟩

private theorem block0:WideCovered band 8650675 8917532:=PRB band Z1.f1873 8650675 8917532 (WB 206367909016 16 0xc719a3c62e169eb4f888121cc719a19a4753876b3787c1ecc309a130822d6a9d738771bdc309aee17b7d9a807287218dc309a6f5951695511686d15ec309a69e011684bde086812ec309a58c141424f9358630ffc309a542ec9505d37585e0cfc309a382885052a4548590a0c309a2c62e914bd774854070c309a121fe89eb1b7384f041c309a09be88a4cb97384c829c309a03e8db205df4284a011c309a2a6a3335f26328477fac309a82206f6af2081844fe2c309b29bff353cb0b08427ca) (by decide+kernel)

private theorem block1:WideCovered band 8917533 9245970:=PRB band Z1.f1874 8917533 9245970 (WB 206367876248 16 0xcb29a3959e1081a6f11a2a259653441991346cc1de33138b2ca6d324577f9f8fbc63a59e594d36b44cbcda4f68c2483cb29a67fb517eb1ecd17a8a996534b06a22c7029962e10932ca693b1fe5b742a2c599fae594d1a55c49d4f5a48ae3c6cb29a3fa522971b40715272f96534589a1ecfa530e290d9f2ca6de8c85d5bc6f144f99c638cd379258b610d4189a308c719a6af2f16f9d16312a5b38e334c679e2d847d46240aa71c66973f305dbc008c4593d638cd56a4f98e5e56088624b) (by decide+kernel)

private theorem block2:WideCovered band 9245971 9574409:=PRB band Z1.f1875 9245971 9574409 (WB 1306953245816 16 0x68ce685afb613aa42692180968ce6858a2e13ab54691c7d968ce685595013afd5e9177aa68ce68517a013b939e91277a68d2684bb9013ca03e90d74b68d2684663813d293e90871b68d2683a82813fc8269036ec68d2683190c14065758fe6bc66ce6848e40135fb3c8f968de7ce681f05414008348f465d64ca6c952d2cbebdc38ef62e64ca6c59a4ec39aedb8ea5fe64ca6c2332ebc46f938e55cf66ce695cb8a6413b9a8e059f66ce6905b585eb26b98db57066ce6889f6054e88188d6541) (by decide+kernel)

private theorem block3:WideCovered band 9574410 9923374:=PRB band Z1.f1876 9574410 9923374 (WB 206367742008 16 0xdb59b5aaaacba1fcbb59769a4de13bd4382225b2b3f4d26f1834a108092cf541a693789aa504dd8962a70d349bc030a812bd4aed20e9a4ddd9e53ff9aa5628474d26ed7ae9fb1d12a73c5a6937605f4fb50494e9b3d349ba96f27bd244a4cc269a4dd14bd3d62a25125534d26e6c429e739927f24ba693725624f1d9a93a8f5d349b894c27827549ac63699cdbf5053bc0a24c225b4ce6dd71a9dc0952570cfa6736e6b94eae72926838) (by decide+kernel)

private theorem block4:WideCovered band 9923375 10580251:=PRB band Z1.f1877 9923375 10580251 (WB 206367774776 16 0xdf79b0ee3980f24685c46f7de6c2d9a5f5199a0d0bcdf79b0d78d7a8a7680c1777da6c383e5e03339f8ffedf69b08f197615be7bbe837da6c0bd05cf27b9e4f41df69afcad972454676bb8b7da6bd5995c3c599d0e83df69aebe896ea26e71b8976da6b84615b6fcf9bcdc6db69ad76616d53ee6cb59f6da6b4eed5aebb79a8d08db69ac41b96cd0b667b2a77da6a92225c16e7994c4adf69a73c49750d4e62afaf6da6a8ecc59bee4980b8c) (by decide+kernel)

private theorem block5:WideCovered band 10580252 11237128:=PRB band Z1.f562 10580252 11237128 (WB 206367774744 16 0xeb99b50c39bdee1d5bb8473ccda5524dc4736ab5aa79e66d13af6cfd97546c95cf3368310b5eaafa995ebe789b428d5aa3d5d47ac6f3c4d9ef6ad34e9aa154bb9e26ce48968c09d4f699fcf13667ac33e0b7a71470e389b2e3f19afcfd33a0971c4d94510cbaba2974ecf8e26c9c0964ea394a66a9c6f36522631ea4ba492f5e379b24a5d8c8edd1f94b71bcd8ffb2c4eb128d48df8de6c695e6194a34563b1bef3629c3b073d1a21179) (by decide+kernel)

private theorem block6:WideCovered band 11237129 12263498:=PRB band Z1.f1878 11237129 12263498 (WB 240727546968 16 0x81e4da37996d79c72ec812a0793671241aa14f0b9df8d7fe4d936a666e3d92e27b3dff73627e018e64e0b75e117fdcd861f161b7a42d8754dff73615e657ea354b4dc967fdcd7fa3d5fe65d2ce6f61ff735d95fd813534b25b1b81dcd6d729eedf26ac46975ffd3524e096c8849afd9a075d4d5b0103bb7f12bce505d7535659b8ebe5ecae98e275d4d57cf43a42f82b7e20dd733560f08e62e18ad582475ccd56d2138e1422b2df15d733556168e13d04ac1766) (by decide+kernel)

private theorem block7:WideCovered band 12263499 13577252:=PRB band Z1.f1879 12263499 13577252 (WB 240761136248 16 0x95026b7a8b115276399e58492604d0a16a18cafa4f37ad9e4c09b7a6bb6a0b415665554c881353fc80e1a2811cb69eb86f66e023b4f816ec194525b0decdad0551bb043a323a1c213d9b366ce3205cb463d3d9427b3635bc45bea790c666f584f66c1856ca8c85018a4c6f09ecd7a14f13cfc0e30f95ea0bd9ae179124f18a861525e417b35a0e8644fc6f8c163fe82f66b2492483a0ed180468105e4d5e6380f9e5de2fb8a0e03c9ab259e1defca05ed0e2c079355132438f8858bc6108) (by decide+kernel)

private theorem block8:WideCovered band 13577253 13904930:=PRB band Z1.f1880 13577253 13904930 (WB 240727549016 4 0x97e4de1ad92fdc93ed42c2299b4dbbde2c6e503ad2ee5d95f4daa3513c77cb5d1ad9f97dcd4e448db4c5a8d06ce2) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8650675 13904930:=(_Q1 band 8650675 8917532 13904930 block0 (_Q1 band 8917533 9245970 13904930 block1 (_Q1 band 9245971 9574409 13904930 block2 (_Q1 band 9574410 9923374 13904930 block3 (_Q1 band 9923375 10580251 13904930 block4 (_Q1 band 10580252 11237128 13904930 block5 (_Q1 band 11237129 12263498 13904930 block6 (_Q1 band 12263499 13577252 13904930 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 11)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:11≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤66)
    (hT0:3003≤T) (hT1:T≤3315) (hnu:8650675≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤33234960734882178:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCW
namespace CZN
open AI AP AN
noncomputable section
def band:Band:=⟨12,43,4299,4332,10715462655907075⟩

private theorem block0:WideCovered band 5636041 9449929:=PRB band Z1.f1881 5636041 9449929 (WB 212809079928 25 0x6205fbc0b7a32da1c9031c9c40bf7802645f46c91f5e358817eefd1c8ad85523cb1ab102fddf3891388ee4754dde005fbbd8d222af548e270cc00bf7793243c64b91b48bb8017eeeeb486a4e723486bb002fddd4a90b1b7e464f7fe005fbbc2f212055c8c1c50c00bf776e941d84d91733438017eeeab682df5322c5bc7002eddceb5041b8a454a216005dbb91020634348a1193bc0bb77017405de39131dc978176edb8e7fe65b22430d2f02eddac54fe15664444c2de05dbb3ec1f894d48806d6bc0bb764403edfda90f084f78176eda987ced1121c05dc188ddc02d40394b5c33f6402b27b8037803d86a85fc1904f4f7004b0045fe309ed7608c96e00700056ee20baff81001dc00f400ad603f6b4282003b801e001592876ab92) (by decide+kernel)

private theorem block1:WideCovered band 9449930 9917760:=PRB band Z1.f1882 9449930 9917760 (WB 206366628888 14 0xcf0de54154051ce5d55033c37934d4f655d96d4adcb0de45113a419e5947fb2c378f2c4db8c195cf4fcb0de348533bdca5532832c378de54c2eec94c9f1cb0de31052e1926511d0b2c378a934adcfe93c493cb0de236928c9b64d078f2c37871149860c92bf34c70de15ed23f2fe48f2171c37838c484be991b9d6c70de06051e5afa44dc9f1c3782e946e2e590b478) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5636041 9917760:=(_Q1 band 5636041 9449929 9917760 block0 block1)
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 12)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:12≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤43)
    (hT0:4299≤T) (hT1:T≤4332) (hnu:5636041≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤10715462655907075:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZN
namespace DDN
open AI AP AN
noncomputable section
def band:Band:=⟨12,44,4211,4307,10542790073267256⟩

private theorem block0:WideCovered band 5767112 9219520:=PRB band Z1.f1883 5767112 9219520 (WB 211735370840 22 0xc017f14ed3407b80e32b703005fc5214d003c8f8c2989c017f153f63f91d8e2e954b005fc54054fd32e38b211bc017f14b1d3ee563e2a7393005fc516a4f9f32f8a18adc0177140703e3da5e2651d6f05dc4e620f74d2b89103ebc1771327e3d9a45e22301ef05dc4a348f4b01f8807d0bc17711df63cfb8de1e0e66f05dc4383cf2144386ff62bc1771203b3c526be19ecaef05dc4b378f03ef385f6f4bc177125233bdf4ce15caf2f05dc472c0efdbd384ee85bc1771103a3be840e11a93ad05bc47080dc681383e617b416f1190136dfbfe0e8ff01057c005e801e57a8361e006a970009f002ad7605440c1003c002c000aa4c790d90) (by decide+kernel)

private theorem block1:WideCovered band 9219521 9761074:=PRB band Z1.f635 9219521 9761074 (WB 206366661656 16 0xcb1e31aa092c73929e265963c6429522ff4a51b3ef2c38c5e7a40e00c9f46265871872347851b93648dcb0e304ca8de2c525c0ad8e1c5f42d19231249707f1c38bc1ba2e0b448ebf3e3871724e4512339153b0c70e2d9b4890bfd219ef38e1c5c8350f70e6412d0b1c38b72221bb44c7e385e3871699f42f0f68f42d4c6fe2c98a84d7871d7d3b8dfc58119080e7e38e99b0bf8ad59a0bbb846db17617f1557c410ffe8d31f7) (by decide+kernel)

private theorem block2:WideCovered band 9761075 10098995:=PRB band Z1.f1884 9761075 10098995 (WB 206366661688 9 0xdd1e3a48ce138a39a1933cf1e368009f28be9912ebcf1e368649d3340988eb4cf1e35e989bd5d0980a7dcf1e353c49a4fbc978646cf1e3486898ba4497020fcf1e33e4c9767e4967dd8cb1e3325095caa895f9a0cb1e3278894727e957569) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5767112 10098995:=(_Q1 band 5767112 9219520 10098995 block0 (_Q1 band 9219521 9761074 10098995 block1 block2))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 12)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:12≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤44)
    (hT0:4211≤T) (hT1:T≤4307) (hnu:5767112≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤10542790073267256:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDN
namespace DAH
open AI AP AN
noncomputable section
def band:Band:=⟨12,45,4126,4283,10877969545853830⟩

private theorem block0:WideCovered band 5898183 9116660:=PRB band Z1.f1885 5898183 9116660 (WB 206366693464 30 0x30bf98965df141a71637e985fcc3ca8f783ef8a9635c2fe614f97ae945c5083b617f305fa3d313be262adf0bf980691e791e71209f17ddcbe9a8f28ddf887f39beee5e4d57892a1c3fcbcdf772e8f0bc1862e1dceeafbb96e181dfa16f0ddbf77ddcb5354edf24386683cbeee59ace76ecc3c2f13edf772a8cdbbbad8e1572fafbb957959dbec6709adff6dbcbaf3ad98be3845140b6de5d3286c662fc207305b6f2e77bb612c3e0f2e02db797277daf06370711436dbcb88b8d6b45b8345c1b6de5bf016b1591c181715b6f2e1a9b553a7e0b000adb7975329a903c704fa476dbcba3c6d41c8f823a43b6de5ce8069c949c0fbb25b6f2e5a8b4cd5de06d212db7971e89a56d7f02e34b6dbcb8730d22ba7812ec5b6de5bfd168efedc075f3036f2023700de6ca02a41815790127006f4b2ff3b0e091c8023e00a81c7b6f8e) (by decide+kernel)

private theorem block1:WideCovered band 9116661 9664486:=PRB band Z1.f635 9116661 9664486 (WB 206366694424 16 0xcb1e681b5465a5b9377e6cb0e67a2945d0a892f227cb0e6711545239d926c68c70e668d744972a91e6a9c70e6602a4409549160eac70e655834350b490db2bc70e6573842bad690556bc70e657f84249318fcfacc70e6507941cb498f49edc70e648dd41544d8ec42ec70e6414240ea218e3e6fc2fe6391b4080368db8b0c2fe62ed03fec508d32f1c2fe624f33f7e2f8cad32c2fe619dc3f0e118c2772c2fe62c4e3e724d8ba1b3) (by decide+kernel)

private theorem block2:WideCovered band 9664487 10280230:=PRB band Z1.f1886 9664487 10280230 (WB 206366694488 15 0x37939efe91c3a12b9cdd26de3e795bc709e66a6f4f6378b9d990dcc4f159ac85acf2e6d7e94f5694266f3733cb9b301d39491c99371dcf2e6c13e4d7295262c5773cb9b111d32c510982b9ecf1e6bad64be2be25e977f3c79ac9ad2cd334972020cf1e6a9d04a868c25a69872c79a7fa126e7309614a2cb1e6967e4901792563b8f2c79a33d52136d8950924cb1e686f14796cd2520d932c79a241d1b905093fda5) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5898183 10280230:=(_Q1 band 5898183 9116660 10280230 block0 (_Q1 band 9116661 9664486 10280230 block1 block2))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 12)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:12≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤45)
    (hT0:4126≤T) (hT1:T≤4283) (hnu:5898183≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤10877969545853830:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAH
namespace DBG
open AI AP AN
noncomputable section
def band:Band:=⟨12,46,4045,4258,11282054829422862⟩

private theorem block0:WideCovered band 6029254 8799742:=PRB band Z1.f1887 6029254 8799742 (WB 206366693496 37 0x2fbfa80c99d254c58645fec2fe99cb375103b616fadf0bfa2d519dbab8d853770badea7d4569d975612c0a6eb7a9dfe9a636fd846c86badea7258694105610a38adb7a9b14da3cd0583e53fb6dea65dc68a41f60e866edb7a97b7da14d85835df8b6dea574468008d60c6952db7a93b5d9e9de582d6b1b6dea58ce67402560a4c36db7a9ab759b4cd5824f69b6dea6ae4668e7b6082f16db7a99949995e5d81c822b6dea617866210160611fadb7a9712d97ab4d8140dbb6dea56bc65b4f7603f4dedb7a942f595fe2580b994b6dea4a38654a97601d7c2db3a90c5d94589d80324db6cea3b3864e21b5ffbaa6db3a8c9cd92ba857fab06b6cea2894647b9f5fd9d8acb3a875599125357f23bfb2cea105c6417bb5fb806ecb3a8048d8f9cd57e9c78b2ce9eef063b7bf5f96352cb3a780dd8e268d7e1530b2ce9e25d635d2d5f74630597a00de803b0247d8de9064e8037b00ebf0df5291419fa008800218127cc2fe063e801790053045eed1c013fa00610014b48799754041e8018400529a1d5746c107a006040148906ce8a9) (by decide+kernel)

private theorem block1:WideCovered band 8799743 9353840:=PRB band Z1.f1888 8799743 9353840 (WB 206366693400 16 0xc70eb0b007e3e3f1d74e18e1d600eefadcd238cca71c3abd46df278646d5f1618757459bde60d8d249bc2feadab87aee8b193aa985fd5932ef3a63a3058370bfab2f21e358e45c763617f56d613c08548b077fc2fead06b77808f15006f85fd589f0edeb2227e3c30bfaae035d9c21c4b8d4e17f554903af98f88ea62c2fea975f757f6d10c63785fd502f0ea318e1f6f52fbfa9948dd316543aa46df7f51f0b3a48e686cd46) (by decide+kernel)

private theorem block2:WideCovered band 9353841 9907938:=PRB band Z1.f1888 9353841 9907938 (WB 206366694424 16 0xcf2eb961a486a76972ee2cf1eb8a8947c2c096a79bcf1eb7de1470b0b962054cb1eb7087464c0b95990dcb1eb639c459dd99511c6cb1eb560a44ec44948a7fcb1eb5ee34444af940338cb1eb54ed43be7a937bf1cb1eb4a9e4337e392f4a9cb1eb3fe342b090926d62cb0eb34a24227e991e61bc70eb28bb419d5b915ed4c70eb1c0441102590d78dc70eb0e45407f1d905046c70eb1e403fef028fc8ffc70eb14e33f86fd8f41b8) (by decide+kernel)

private theorem block3:WideCovered band 9907939 10461465:=PRB band Z1.f1889 9907939 10461465 (WB 206366727288 12 0xd73ea2c75ab37b509fa119d73ea259baac72289f1c0cde7ea6983b739fd49e94c5de7ea393db7541f39d8637de8e9db78b845d4a9c77a9e27e86c82bd744299b691bd32e9e9f5a6890c09a5a8dcf2e9e325262036899d346cf2e9dc2a25b6a18994bffcf2e9d4f8254bd4898c4b8cf2e9d32a24df558983d71cf2e9d0b2a488cc097b62a) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6029254 10461465:=(_Q1 band 6029254 8799742 10461465 block0 (_Q1 band 8799743 9353840 10461465 block1 (_Q1 band 9353841 9907938 10461465 block2 block3)))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 12)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:12≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤46)
    (hT0:4045≤T) (hT1:T≤4258) (hnu:6029254≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤11282054829422862:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBG

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option autoImplicit false
namespace DCI
open AI AP AN
noncomputable section
def band:Band:=⟨13,42,4152,4261,11951205757056601⟩

private theorem block0:WideCovered band 5504969 8832207:=PRB band Z1.f628 5504969 8832207 (WB 207440403576 27 0x1830dedce291a7c1e1b133f05fbd7ced229403c340bbe0bf7a653244173f863e20c17ef428d4b56c4d0bf5917afde63589cdc07616ddc6f5fbc027937b556c2ba0cdebf77fc3266824d8530c2bd7ef3aa44c6d0bb09dad57afdf3368972cdf612a84ef5fbf07ed513f4e42335ddebf7da5a2a01d2c842364b976f2a743c325c707c01972ede37e477d69ce0e72d6e5dbc27a4ee904dc1acaedcbb7794e9dad873831606b976ed4df3a90d9705a55d72ede2ed07444fae0a3d5ae5dbd0398e73f91c125ff5cbb79d609cd80cb8208a7b976f33ce3995387038a9f72ede57a073016ce0607e2e5dbc84b0e4d0a5c09f505cbb78ae69c94fcb80fb49051ee05cc01afe15016fe20a4dc037a00f04a600c5081cdb802dc00a9843f0b4282077006380150d875ab92) (by decide+kernel)

private theorem block1:WideCovered band 8832208 9297676:=PRB band Z1.f629 8832208 9297676 (WB 206366661752 16 0xc6fdf8e0e9f19432377c331bf7dbf4277f0fc8d585dc6fdf49f49ce86b23346bb1bf7c5e726f81648c4affc6fded5da9c6a9522f11431bf797cba7057bc8b3da1c6fdd699e9ca15722adbc72bf78117685e9e48a3042c6fdf211c9e5ff2e26a64f0bf79d00a2e4cba8922e4c2fddf21c88fb88a2270d31c777a24ab82531881585c71dd1dbcb0c9c461f48bb0c37c8dc24f19b0878ed6c30df0c9692991c21d2dff0c37bd9f2486010870827) (by decide+kernel)

private theorem block2:WideCovered band 9297677 9849342:=PRB band Z1.f630 9297677 9849342 (WB 206366694424 16 0xcefde35045bd7bf9649fecefde3acf5aac0595c34fcefde325559b8cf953ca0cefde2b225904a094b5f1cefde22225813bb942f42cefde18b85721af93a893cb0de0ec3562cee9321e3cafde05f4558144929b34cb0ddfa7b54868d921485cb0ddedce538318918dd6cb0ddfe0d52b230910727cb0ddf6b5521ce6908078cb0ddef7e51a4ca8ff9c9cb0dde68c5103578f731acafdddcb45063f48eec6acafddd1a14fc6828e65bb) (by decide+kernel)

private theorem block3:WideCovered band 9849343 9917760:=PRB band Z1.f630 9849343 9917760 (WB 206366694424 2 0xcf0de48e35de03f975540cefde40fa5d268b96d0ad) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5504969 9917760:=(_Q1 band 5504969 8832207 9917760 block0 (_Q1 band 8832208 9297676 9917760 block1 (_Q1 band 9297677 9849342 9917760 block2 block3)))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 13)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:13≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤42)
    (hT0:4152≤T) (hT1:T≤4261) (hnu:5504969≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤11951205757056601:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCI
namespace DCX
open AI AP AN
noncomputable section










open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DCX
namespace DDH
open AI AP AN
noncomputable section
def band:Band:=⟨13,45,3933,4218,48804309514098683⟩

private theorem block0:WideCovered band 5898182 8162281:=PRB band Z1.f631 5898182 8162281 (WB 206366728343 45 0x16dbd44c1d72910877c8be9b6de8cd00bb449bbbe348bd967515648984c259f11916cb3a8f1e64bc0c4cf846e9659d46cbd25e12667c00a2b2cea2e3512e45b73deee8596751f9709d9305beeebfacb3a876d64b71e9cf7305b659d426e625a43ae7b755bb2cea0a1112d97573da944d9674fed989689dd9ecbedecb3a7bfa44b27cfcf619cd659d5abde37b9bfdfaea14b2ceabe189be4ea2fd63a1596752de1cc679bb3ea91c2cb3a8fc0c6375ce9f5033f659d43b963203b74fa5ecdb2ce9b96596aa67ebd1dfdd9674fde3cdb2bfb7e864a6cb3a770086ded0abf40f83659d36f7d372cc05f9f658b2ce98de19bb8242fcf277d9674ae768df127d7e74e1acb3a422a862da8a9f3843b659d195ea31c2724f9b0b4b2ce87f13991868e7ccfa5d967428444c5cfd13e6378acb3a07ad663629a9f30a5d659d033fbb1f8bf4f97c7ab2ce85b26d92658e7cb9e3596743f5d6c8ba8f3e5ac46cb3a2b0595ab3feaf2cd6f659d1746ab26980cf9625da2ae807a780682da3cb018535f403d20034174fe5780e6a3a01eaa01a0ac7f2b7ad3d3d00f5200d05637959a8a6be807a580682c57cabbdc94740e8b80cab989e55539e93a074b40655994f2a1e80cbd01db601994c1f9483f060e80424003611cbc814d833f40129000e7923e1dd50117a0040e0028820e83a36083d0020200142386b68a9) (by decide+kernel)

private theorem block1:WideCovered band 8162282 8447522:=PRB band Z1.f632 8162282 8447522 (WB 206366728344 18 0xbaee98f730fc82b2203988aeb7a598d63bd352780a07ebaee946150ef583de016b6eebba466f83be9857801537baee8d8150f06999dff3e52ebba236343c858b77f89f0b6de8dac796dab6d9fd1136db7ac104665cd4847efea9b6deb8a749e56fbd5fae41adb7ab6996655bd347e7362b6deb56f01e755955f8b6fedb7aa8250659c0947de81bb6dea9cd41af5a10df689e2db7a75f5a548b4d27d5cd4b6deb394827aff5c5f45cc2db7abcb16a00d8a17cf45eb6debae2537782341f34632db7ac289ae0925707caebb) (by decide+kernel)

private theorem block2:WideCovered band 8447523 8732763:=PRB band Z1.f633 8447523 8732763 (WB 206366727288 16 0xbefe90736a6259cd85405bbefea6da5a8d772484fab7befea60e3a8c43ec84b514befea4f23a87dcb4846f70befea8f8eadd2e1a8429cdbefea74a72d7a38a83e429befea2a1b2a3c24b839e86befea3343ad413528358e2beeea017cacfbdb283133fbeee9be2c2cbd37282cd9bbefe962402d5605a8287f8befe8c01aad776e2824254befe8864d6e118f281fcb1befe83afb9e5831981b70dbaee9b4739f8fa28817169baee9a3d99f8d720812bc5) (by decide+kernel)

private theorem block3:WideCovered band 8732764 9071487:=PRB band Z1.f634 8732764 9071487 (WB 206366794872 16 0xc30eae82ecbfb03148a6b7fc30ea87270add08c489e037c30ea4b2aea87e5848954f0c71e87af362a329db88c9a9c71e86ed182a602eb888406c30e88193023ebe92883e62c30e887ddc23a040287f8bfc30e884fa0237a55287b31bc30e881c142356f12876d78c71e8d5ec131323618727d4c30e88886a26ff80886e231c2fe882ee226d8408869c8dc2fe87c2d026b6c308656eac2fe873c04269e018861146befe867b04262c63885cba2befe858794261d7988585fe) (by decide+kernel)

private theorem block4:WideCovered band 9071488 9641969:=PRB band Z1.f635 9071488 9641969 (WB 206366727192 16 0xcf1ea8c85a70f71498ff8e58f53fe9135a11a4a52a72c7a9c78e9960892412c5963d4c4974bf578917e1bcb1ea5803a59b0148796a658f5372e529f416419e372c7a990bc9412111fb88d963d4b216499b7d8f50ffcb1ea4c97249ae4c762dc658751f25123663a38e9c32c3a8b5429114371b5e53961d43098484d218d23e2cb0e9fcbf2415fd464c4de5874ead8120e83a3035532c3a65dec914a8717041b963d23e0d49f7948af6c6) (by decide+kernel)

private theorem block5:WideCovered band 9641970 10212450:=PRB band Z1.f636 9641970 10212450 (WB 206366793848 16 0xdf3e90e7d08ecdb4f37a8c5be7d20037d186f55e6d246f6cfa3aa6ca1d08afcd5eea6d9f46aa02428c1d79a328ddb3e8b780e837b60f334e8db69d10d29105fc1be646fff6d3a06321216a69fcc485c6f9f51f021cd9c72e980571db4e8bf882768401b2ef455b69d145d54e5cf0d25bbb8b6d3a1c29f9a61091cb31cdeda740f5dd36a638395d854db4e8ee42588c2cc52a9a1bae7d17d710e79fba653071b5cfa2a5971d0670cca1b3fe99f457e8e2db4c2893ab38) (by decide+kernel)

private theorem block6:WideCovered band 10212451 10461465:=PRB band Z1.f637 10212451 10461465 (WB 206366761016 7 0xd73e9c83b4d0b8079fa119d73e9c0550cdd7ad9f180cd73e9b717cca69139e8cc5d73e9ae64cc6f7e59e017ed73e9adfe4c41cbb9d7637df4ea4fb2129c9cc9ceaf0df4ea3714d236a189c5fa9) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5898182 10461465:=(_Q1 band 5898182 8162281 10461465 block0 (_Q1 band 8162282 8447522 10461465 block1 (_Q1 band 8447523 8732763 10461465 block2 (_Q1 band 8732764 9071487 10461465 block3 (_Q1 band 9071488 9641969 10461465 block4 (_Q1 band 9641970 10212450 10461465 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 13)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:13≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤45)
    (hT0:3933≤T) (hT1:T≤4218) (hnu:5898182≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤48804309514098683:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDH
namespace DBO
open AI AP AN
noncomputable section
def band:Band:=⟨13,46,3951,4288,33078420730379481⟩

private theorem block0:WideCovered band 6029253 7975796:=PRB band Z1.f638 6029253 7975796 (WB 137647014007 16 0xea3b9c36c7fef366e9d577370d8b2be64106dcee745b1257cb686b3fdce63623e7949d9ea7b9b86c4e3f24d4b6e773a0d87d7e40dca55ee761b0dcfc701f2a1dcee3618df8bd0a233b9de6c2cbf133ac24773bed8517e1da8c44ee781b092fc29b7883dcf036109f8303b107b9de6c1e3f01a0e20f6b3273e55de00e041ecddc83727b334c883d9310a1dc6d99a7) (by decide+kernel)

private theorem block1:WideCovered band 7975797 8119984:=PRB band Z1.f639 7975797 8119984 (WB 206366727287 19 0x1659dd2d3a4be8179ef9ac2cb3bbb37cac8d643de1bed9677707a5587b807ba049b2ceed407aafdb40f6fa2b659dd8bcd55dce01ed6786cb3bad950ab88cc3d9b57596775280556cc087b137ab2cee57d72770ebbf5e08d659dc85e74ee1d77eb344acb3b98860ab91d83d54efd967723ab5599cec7a86abb2cee23702b55db0f4c6ef659d935312153b55e9010ecb3b80670bdfbe87d0e8859676d6ff950d1b07a0b76b2ced8c6f2a2db68f3f3b9659dacb9b548de91e7a10acb3b4e338a99d943ceb545967681d3154884879c50e) (by decide+kernel)

private theorem block2:WideCovered band 8119985 8390338:=PRB band Z1.f640 8119985 8390338 (WB 206366762104 19 0x175dd93d180769261e001b0aebbb2053c0eeac53bfe02d5d776349261dedbbf7f79f2b6ded46b0c68edbdcfe67156dbdb8c550cc74ed9fbb48edb7b85a251e94c0abf535ddb6f70340e3d19e9d7e6054b6dedf3bb87a5d8eafc33d96dbdbb9a98f5e43f5f74e16db7b1b2cc08bf4a23ec68edb6f635704136c33b7d46b6b6dee95b38dfd41f4fa009d6dbdc91be1bd1d909f3746edb7b7c475386f31d3e5cf3db6f6bbf6a73772927c96b3b2ced19db535f6c32f8e6ff6dbd8d4ea6846f325f14132cb3b5516213102603e168c59676a7fd02609c507c09e4) (by decide+kernel)

private theorem block3:WideCovered band 8390339 8678715:=PRB band Z1.f641 8390339 8678715 (WB 206366727256 16 0xbefeee008aac40ef08da777dfde0de35c1830a109b4efbfbba062b72be541f035df7f7619916c8072839a03befee957d2d5dce506a7397dddcb48c5a6f79a0c34d2fbbb82394b4978f416366df776c79b169b266828065befecc044ad8e6350473fd7ddda6ad73a4852607ce5afbfb34c0275c838c0d697dd776f0f80ed64d08166c7baeedce7c9da3b290240c175ddb6c053b2c6720367e2ebbb65f7e76771a4049c8dd776b6fa4ec5ea4804d29) (by decide+kernel)

private theorem block4:WideCovered band 8678716 8967092:=PRB band Z1.f642 8678716 8967092 (WB 206366760056 16 0xc71ed2633552af674469da638f685830aa6d87a2235330c3b495c548943bb108dc9861da8365a3bf22d88007cc30ed3b2b11d0652c3dd0ae18760a68cb9f85921dceb71c7b80ef7e5493a90e5a8d861da8a38275475386e6dec2fed364d137dc19c3503be17f6936c29baa6ee19683f0bfb444154d1e3c70c275185fd9eed9268fecb85cd40befecdd31141317d42c36ce18766a8a4cad6ec61501c6fbfb5c0e5522c0a109f4157dfdace5028d953884b3a2) (by decide+kernel)

private theorem block5:WideCovered band 8967093 9525821:=PRB band Z1.f643 8967093 9525821 (WB 206366793816 16 0xcb1ecaeb904a76bfe4568f72c7b2b632126b08b90cd6dcb1ecb278a48ecc8e41027b2c7b2be9b9225adb8fb3cfcb1ecac5d848388ae3c9c032c7b2a19891f25f78e9a31cb1eca3c54476100e38358b2c7b279f811c985f8d8093cb0ec97f98471a5ae33cf132c3b239e391bbc138c66f5cb0ec805f846f0d8e2f689b2c7b1a1e311dd86b8b4d57c71ec9dec272a2bca2b02232c7b8e9a6627ced28a33b9c70ecc05485e753c6269bab1c7b2759e951a614891a1b) (by decide+kernel)

private theorem block6:WideCovered band 9525822 10102575:=PRB band Z1.f644 9525822 10102575 (WB 206366728312 16 0xdf5efad809fb449bcd1397efaf79cc8902c8ada66697f7d7b85d6277bd26b321b21bebd8230fbdcbdd59880c1db5ee696719bc5fa4bf9f96da77b7aa4ea29c6e5d9c8f6d3bbef0075ae1e72db4a9b69dbd8d6353cdda964d85db4ec0bf59ccc2f94ae05b6ba77e2c4cea4dd0654cf9b5d3bdbd3073709d3294e2fae9de12253aa2239941a48cf1eefabe934acf449c6bce78f77634498dfa224c02ab2c7bb733a4bb1f0124e7b7963dd9c052598fc891e70c) (by decide+kernel)

private theorem block7:WideCovered band 10102576 10642700:=PRB band Z1.f645 10102576 10642700 (WB 206366761016 14 0xe89ef2a2edac716fa2650cdb4ee28460d4e881a14db2db4ee1e078d1898ba0c0e3db4ee13c40ce3191a03414db4ee09710cade159fa745e34eeac6ed2c4f029f1a76df4ee8a241257b9e9e8da7df4ee644051f3c5c9e00d8df5ee2c1dd13bf9c9d7409df5edf35d10dea749ce73adf5edfa14d08ab009c5a6bdf5ee3897d006dcc9bcd9cdf5ee21288ff6a649b40cddf5ee0587900167c9ab3fe) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6029253 10642700:=(_Q1 band 6029253 7975796 10642700 block0 (_Q1 band 7975797 8119984 10642700 block1 (_Q1 band 8119985 8390338 10642700 block2 (_Q1 band 8390339 8678715 10642700 block3 (_Q1 band 8678716 8967092 10642700 block4 (_Q1 band 8967093 9525821 10642700 block5 (_Q1 band 9525822 10102575 10642700 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 13)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:13≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤46)
    (hT0:3951≤T) (hT1:T≤4288) (hnu:6029253≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤33078420730379481:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBO

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option autoImplicit false
namespace DBY
open AI AP AN
noncomputable section
def band:Band:=⟨14,56,2954,3606,42424075804590334⟩

private theorem block0:WideCovered band 7339962 7505493:=PRB band Z1.f1308 7339962 7505493 (WB 206367842391 23 0x29a635cad094b7360f28655a698d5e84e525223bc977b29a633ceea4f71aab723582a698d31448527e12bc834629a63446b41489490f1e4aea698ceb5d651e957bc6f1169a632ed4bd4754b0f193dba698c7c7a551fb3bbc5adc69a6309627949f300f14307a698c35dc73311ed9c46a7a9a630bb944cc6256710669a698c263b9332c6a1c3c8d29a6306c170cd50c270ddffa698c0bb20339c699c3272a9a6302ccdad0833070b595a698c31b36b5217a9c285828a2349cc5cf8faaef08d2ca288d3e93b3d1fbb3c1e3de8a234e8100f37cf6f064c2a288d354b83c9ec43c142368a234c19a0f1790ef03c58a288d2b5093c1db0bc0a08e8a23350430ae60ea7013ee) (by decide+kernel)

private theorem block1:WideCovered band 7505494 7671025:=PRB band Z1.f1132 7505494 7671025 (WB 206367875159 22 0x2aaa340a7e4fbe54cba8678d554640b9e1154fcaf4e488aaa8c74aafa290595e9783d55519786df7acdcd5d24ed2aaa326c32ef465bbba35a555546387a81e7da937442e1aaa8c389fbbd23b12e834ef5551830c47fb830c5cfc836aaa3205271a85ca739e4d1d554609454cfaad82f3a13aaaa8c0e5f21f53711e71a0b5551810bb73ebf47bcde342aaa3005a357e26e679b24dd55460aa27f00215ef35066aaa8c5a99ce20a085e678634d319a3fa751a6625cc9ff29a6321b2266ad05a7989e4534c642585cd4f552f2ff93a698c82d991a9b335e5d6bd4d3190159c3518263cb5ca69a631f91e469dd8679617a534c647eb70f85e9872aebf) (by decide+kernel)

private theorem block2:WideCovered band 7671026 7836557:=PRB band Z1.f1309 7671026 7836557 (WB 206367942743 16 0xaeb8c1b971c1fcb6abef271b5d7183059383fac5cfddac92bae304f77187fd59cfba15d575c60b956f178e71d771a50aeb8c0cd6cc2f1f36eede3cd5d718037ab25eb9deddb25f6bae3061183cc020c6bb5089d75c61d1a1a98d27bf7678a9aeb8d497c0389b0c50eca07f555180f6766666a0dbd89f5aaaa30db06f8ab005b7affb6555461a756e152a168f5d702aaa8c4f0b2840d7674eb5d3155518970b5c7fec109d618beaaa311f0dc0fc7d933aaee2d55462291bb1fd3c9c75355b) (by decide+kernel)

private theorem block3:WideCovered band 7836558 8002088:=PRB band Z1.f1310 7836558 8002088 (WB 206367875191 16 0xb2c8c47ab41aec07ffa1a28b2c8c365881ae9b67f9f1bfb2c8c1ff8d9b8978779c955b2c8c00f005bf6fcaf9a0ecb2c8c139135d0b0ea797882b2c8c94e0a68acc15f95019b2c8ca8f11ea073297927afb2c8cb32b9eb4c62c78ff45aeb8d0078bb1e5294f8d6dbaeb8cf8e82318eae4f8ae72aeb8cef81a30fa364f88608aeb8c971179fe3e34785d9eaeb8c90b371fbca60783534aeb8c899199f9a6ac780ccbaeb8c82fcd1fdda1c77e461aeb8c798f99fcf41077bbf7) (by decide+kernel)

private theorem block4:WideCovered band 8002089 8291769:=PRB band Z1.f1136 8002089 8291769 (WB 206367842423 28 0xb6d8cd1c6b292d3b7fd0b736db19991ec5227fbff97542db63317508a31e75ff1a735b6c65fc379459327fe0c7cb6d8cb884728a12b7fbc8256db1961488512aa6ff6eea6db6329ebdca24203fec99fdb6c64e152142364ffd6ad5b6d8c8ff60284b1d7fa84d76db1902b3a50b71eff4680adb631d91d0aa9d65be78cc5b6c62f393956e19f7cc92eb6d8c707e02eceb25f941896db18c158e5e31f5bf1e16ecb232e61f8da5c3f3e27f8d9646557929b65f667c2787b2c8d80eab476c1d9f7fe3b6591aedb908d88333ef5ad2cb2345f0a8d9614a3dd7255964688a329b283507b85e0b2c8debf666251c43f6baed6591bb1a9ec294a07ecd436cb23580f412ef43cbd8651d9646a7716258f3097ae439b2c8d1f38f44177b9f5779f6591a1655c87428f3ea4d9acb232f8ee0d5c7da3d357e59646542491a9ec607a4292) (by decide+kernel)

private theorem block5:WideCovered band 8291770 8622833:=PRB band Z1.f1311 8291770 8622833 (WB 206367876216 18 0xbef8c8ffd90fe31b620e4bc6fbe3201df63e577d083421ebef8c6f7ff8fabad020bc52afbe31513903db157882a077bef8c2caf58fcdf7a2093e8efbe308b19b42b95ec81fed0bae8d288fc1bbfceee06b7f2eba346763a6d91cbb815d29bae8d09e2d1b276c8e043156eba33df0726c4942b80bb82bae8ce1d2c1b367fce01aabaeba3313fa46ef206b8019dbbae8c9089b1b3e1aedff241eeba321fcf6d90c7e27f7834bae8c320e009acab25fc9d82eba30ae9ba26e83697efef7b6d8c6d8940a5a0d21fb5a36db631ad30429498287eae23) (by decide+kernel)

private theorem block6:WideCovered band 8622834 8953896:=PRB band Z1.f1312 8622834 8953896 (WB 206367842424 16 0xc718c605b11bb339e88a028c718c514de1bbf24e884f55c308c6bdef181430d87fe81c308c7089f18dda2487adaec718c485c91f0e15b875cdac308c7fe5e19da16a870c07c308c7914419c6eca86bb33c308c70b8019b99b2866a60c308c6616319b47f286198cc308c5ba1319bc05a85c8b9c308c52fa319d843a8577e5c308c5c22a1b5fdd1852712c308c49f9c1bc555184d63ebef8d5965c415866884856bbef8d459453ffd208843497bef8d345933faa6a883e3c4) (by decide+kernel)

private theorem block7:WideCovered band 8953897 9284960:=PRB band Z1.f1313 8953897 9284960 (WB 206367808600 16 0xcb28cdc5a8648c59c6d6b0659466a3fe322438e3572372ca33219699114bf1a17739651960fdcc9f4278cbae6cf38c35ad6820d3346350965946750463521f263064ff2ca3361031a8cbcb1790d796519aa5d0d2c98d8b7798cb28cc7f0869a316c59362659465a1f035271362b57c72ca32a0391a81bb3150a3b96518eae24d9468d8a344ac718d108ee6e9bf244f1bb638c681c113760552264a8f1c633c7359b9437912839f8e319b7614dbf16088f0fc) (by decide+kernel)

private theorem block8:WideCovered band 9284961 9864320:=PRB band Z1.f1314 9284961 9864320 (WB 206367842456 16 0xdb58ca8a973ac2dd54b42406bac6653dd96d14526578b675d6335c90cb0963332a8265ae919d95d46c058b8949f8bd748cb791d34c1e1c49fef26ba4633c7c1e144e1e4d70f74d230d48c5130c24d25752fa671a923368b78c259218f0d338d1af2346a6572c8bba4e79c6570b01a08fd1243568b4d230b90c3dcf79a72067f79e51b72d6aae71b828f9254cf38c7c9401c34910c77856e79c63960e0e1bc9463a7f6b3ce3198d5471283431c9e0d96518e214e32785d08dfe33) (by decide+kernel)

private theorem block9:WideCovered band 9864321 10526447:=PRB band Z1.f1315 9864321 10526447 (WB 206367808664 16 0xeb98c737689051975413ddfcf31a3c5a94a386267ff5239e2343242a53fe344fadd0f3c465c4564b27d389eb9fae378d3047c7a03bcf3c30a7c6f1aafff52b66a5a75dab37de34a2139fee90ace6a82efbc6973043e552459c335ee378c63be0c1472e937236fc6f18425d56c5c78e6bc0437da3678aa2f7c4214d2734efb46a7d555eb154299acc2db68d763bc98dcec3321637b6d1aeff412ab2f4661a5d36d635e630a8b8ca84be3e76dac6a0adc5108170972627) (by decide+kernel)

private theorem block10:WideCovered band 10526448 11188574:=PRB band Z1.f1316 10526448 11188574 (WB 206367808664 16 0xf7c8cf18ee8180bd75572bdef9195f13d0056a6aa85edfcf233785d1c97e7cd4bb0879e4659d8539ab149a8d469f7c8c042f699741d1506585e7719ac9ad08503de9e446fcee3341289ea8ef35377ba79dc63ac413fbe556a64dcdefb8cade8289bd1ab4b584ddf519c638cf92c7d29429ffbea328d641f5411252346c75cc6867ff3654b33a3c731eb98d2ef24844ba45464b15cf31a393b0e1461868a0f8fae633ad5d257f0b850f11ef5cc63c21e4c11250a14096) (by decide+kernel)

private theorem block11:WideCovered band 11188575 11850701:=PRB band Z1.f1317 11188575 11850701 (WB 240727547032 16 0x81f46982b73d7dc29b4d3cd81f468ccdd3d1b1a9b432267ff46831b53c38359b3907f7ff4679c1a3c3eb19b2eed881f46694693cd5649b24d3181f4645f893ec3ef9b1ab8a81fc618d704051098b109e37ff465c0bb3841137b0683c7ff465e655345d876afc6957ff46505a0348d336af24ee7ff46318ba4218d35ae83477ff46001b8c2be204ade1a07dec65dad637cfc83ad3ff97dec64718541f1402ac9e527dec6460093f0f9d1abfcac7be46778f537556c0ab5b05) (by decide+kernel)

private theorem block12:WideCovered band 11850702 12512827:=PRB band Z1.f1144 11850702 12512827 (WB 240761134104 16 0x8502341b2455c5546fbb8ee0c08cfc0a554ac50be4c94830233bde3547060af6abb60c08ce5ed74f7724bd0946830233a1d2534d83af19e7e0c08ce0d5a4b2339bbc5f8830233642f9268a7eec914a0bf8cd1068483090ba82ab82fe33229c11b33d2e7841203f8cbe4d644f128b93f5d80fe32dd5790e6dfae276da03f8cb806c424deeb7fc0f80fe32e28f9025ce6dd69a203f8cb20c93fd008b6b8c180fe32ab7f8fc773ad85c6e03f8ca18d93e0629b57574) (by decide+kernel)

private theorem block13:WideCovered band 12512828 12636285:=PRB band Z1.f1318 12512828 12636285 (WB 240761136184 2 0x22a88d5eebf445385381a0fb0a04688c4c8b32a84bf8fe2) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7339962 12636285:=(_Q1 band 7339962 7505493 12636285 block0 (_Q1 band 7505494 7671025 12636285 block1 (_Q1 band 7671026 7836557 12636285 block2 (_Q1 band 7836558 8002088 12636285 block3 (_Q1 band 8002089 8291769 12636285 block4 (_Q1 band 8291770 8622833 12636285 block5 (_Q1 band 8622834 8953896 12636285 block6 (_Q1 band 8953897 9284960 12636285 block7 (_Q1 band 9284961 9864320 12636285 block8 (_Q1 band 9864321 10526447 12636285 block9 (_Q1 band 10526448 11188574 12636285 block10 (_Q1 band 11188575 11850701 12636285 block11 (_Q1 band 11850702 12512827 12636285 block12 block13)))))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 14)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:14≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤56)
    (hT0:2954≤T) (hT1:T≤3606) (hnu:7339962≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤42424075804590334:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBY
namespace DAN
open AI AP AN
noncomputable section
def band:Band:=⟨14,57,2905,3284,41467633654348955⟩

private theorem block0:WideCovered band 7471033 7638132:=PRB band Z1.f1319 7471033 7638132 (WB 206367876151 21 0x555473e02ad1b1e98748c74aaa8e64c07a35fb18e8c7535551c8d7424714fcdd0eb76aaa387607c9005453a0908d55470fa7f71f7bf373e945aaa8e7de7963ac3d2e780f55551e7f688cce0a29ce5eba9a63a3ed665b9a31b9b771534c746c960b620d8735a7ca698e8b63896a1e84e68c2d4d31d124dc2d00019ccc6c69a63a1b720597a32b98ea5d34c7424164b1ec587308e5a698e8216c161cc46e5e8ff4d31cff2cb2bf8699cb80669a639f3fd6576f5eb965d9d34c73d2794addd4172b74da698e5a3e010ba5d1e545cf4d31cef15b2e032edc9e8729a639bbbcc5a183cb928a8534c7339858b34522722884) (by decide+kernel)

private theorem block1:WideCovered band 7638133 7805232:=PRB band Z1.f647 7638133 7805232 (WB 206367877207 16 0xaeb8e2f6d48a97ef1bb8c98575c70caa2c557eeaddbc196bae3831be087aec1ced8f335d71cf61d1c32cd76769ecdaeb8f5c1ffe1cbacc3b3b00d55470a0f726ba6643d934daaaa3a3d874301db41ec48d55551d1e7fd17c488cf5fb9eaaa8e8a79b0bc756a7ae969555476eb9409aaaea1d6a81eaaa3b4e9e24c65aa0eb02775551d88ead24e128c75586faaa8eb9271923a0923a97d1d5547565f2c904f121d41b62aaa3a7b7a04788db8e9bc195551d1ddba238886c74b540) (by decide+kernel)

private theorem block2:WideCovered band 7805233 7972332:=PRB band Z1.f1320 7805233 7972332 (WB 206367908983 16 0xb2c8e017798744e3abe697b2cb2383222da0b48ae797d21b2c8e2f16469595557e55156cb239e579fb84ca64792b89b2c8e9458dae5b6531e40af6cb23d3b9fec48a58078d9f2aeb8e30385482ab6f5e2c49abae38fa0ba2af5818f8885aaeb8e3b9f28ab67f61e17e3abae38e3e192a8530c7836c3aeb8e360c20a8db011e037debae38cb1a529efab477e52baeb8e2f0c3ca6c4811def17ebae38aada3297d9c8779394aeb8e26517ca8c4de1ddab22bae387faa22a370ac7741fc) (by decide+kernel)

private theorem block3:WideCovered band 7972333 8181206:=PRB band Z1.f649 7972333 8181206 (WB 206367842391 20 0xb6d8e431622f01547f3575adb638bec44bab871fcad0bb6d8e187c1319cc15f210fedb6380448ec4f01d7c5b73b2c8e41a8f3a2dc61f0ca9ecb2399ea80e203747c09dcb2c8e5bac738af461ef8442cb23a91c70d80f367bb845b2c8e9fc6635af3a9ee3de6cb23a6aea4d575667b66aeb2c8f403ba6f0d3f3ecf78acb23ccc03db87422fb1516b2c8e8990f34eda39ebb12acb23a0cb14d4c71c7ac37fb2c8e7a61b3502ab9ea6acecb239c05c4d379287a71e7b2c8e63c4a34c7ac9e9246ecb23957374d6084e7a2050b2c8e4255e35ace89e7de12cb238a17e4d817f279ceb8) (by decide+kernel)

private theorem block4:WideCovered band 8181207 8515405:=PRB band Z1.f1321 8181207 8515405 (WB 206367842424 24 0xbae8ece42674ebaad81ef4dbae8f1be4571333c5819db6bae8f4344a6bd9efd814c1ebae8f327d06bee3cd80fa87bae8f1f2386cf723580a8f0bae8efc2436ae2c25805759bae8ed9ded6ecf8c58005c1bae8e9ca687308bec7fb42abae8e1d71b268624b7f6292bae8e0652826be1bb7f39c7b6d8e609d62a31d017f10fbb6d8e64f0f29e30417ee82fb6d8e6b8fa29835797ebf63b6d8e7aef928aa8b97e9698b6d8e908e7306d3607e6dccb6d8e8cb9a3051a587e4500b6d8e70ce72848f917e1c34b6d8e6cefa28417997df369b6d8e6ed102a828da7dca9db6d8e699c52a87cca7da1d1b6d8e5d4ec280edb97d7905b6d8e56a3e28266c17d503ab6d8e5de5c2f265387d276eb6d8e5174d2ec8a207cfea2) (by decide+kernel)

private theorem block5:WideCovered band 8515406 8849604:=PRB band Z1.f1322 8515406 8849604 (WB 206367809624 16 0xc308e948a4332b01e1c23130c23a4bf00d51bae86b72dc308e87f9c34f5f4a1996570c239d61a0cbaadb8613fec308e69bcc3570eaa17099f0c2394a8b8d9c3598570d0c308e29e7c373d986147ce2fbe3e7e0da07c19c84cda1bef8f910408174f4211f026fbe3debac9fd5c78842a72bef8f61d727d4f9c20f636afbe3d2af19f71f68838743bef8f26b107c3d0720cd6aefbe3be8f01f0d36482e414bef8ebb3867e0b0e20a49f2fbe393b271fc2af88240e5) (by decide+kernel)

private theorem block6:WideCovered band 8849605 9183804:=PRB band Z1.f1323 8849605 9183804 (WB 206367774808 16 0xcb28f132d9a6460f1844799651df625b48170e2f42972ca3b78f5696ac3c5bf86e59475a788d2461b8b2d76cb28e7e289a42eb715b7bd9651c6eafb583a3e2a291f1c63cdf326e739b451c57e38c79ed16dad6fa89e718c718f2de81b5c7b5132b018e31e356736d373a250fa71c63b94f9612afec47928e384766588c1840988a0bac708ec544181ad33109e458e11d7444b01a1761ff62f1c639711a79c50843d5f9e38c716035fb0e68875a5c) (by decide+kernel)

private theorem block7:WideCovered band 9183805 9601553:=PRB band Z1.f1324 9183805 9601553 (WB 206367809656 16 0xd348fa4f348e5411d250423a671ee6ec9192b4da477b8b4ce3f0d3cb4163a6c89dd9e99c77588967cf8ad909884cf38e92d5e30bde391feaad9e71d1a43c613eeb23e8eff3ce3a19e38c227da47a913e79c7491cf1bd22b38f0090cf28e7a840326a9f51d5df19e51cda318649412a3975873ca399c4f0c8e7414705e4e79472f39f1922b5a8dba32cb28e5ff6431cbfc51ad1359e51c9bc2c644e50a345c0f3ca3906208d27ec0c662b5e5947493eb1a617508c73d4) (by decide+kernel)

private theorem block8:WideCovered band 9601554 10269951:=PRB band Z1.f1325 9601554 10269951 (WB 206367809688 16 0xdf78e9caba42e474a9cb4ffe378e8ad3a578ee599c11d0e378e0df7a58b75e99b6ea1df68ec0d8c455a3e89acb72df68eebe585fbb2d79a2844db68ea537e4df9cb6998515db58ec9ad643615f598e1e6db58ec07124328135983eb7df68e4026246c1175979b88db58f02b46759e49496f859d758eb23005c1d55396552ad758e8bf6e5c3fb0395b1fbd748f2a14e6a24192950ecdd748f062b86bf2322946b9ed748ed2be276591e193c86fd748e382268b32630932540) (by decide+kernel)

private theorem block9:WideCovered band 10269952 10938350:=PRB band Z1.f1326 10269952 10938350 (WB 206367775896 16 0xf3b8e7bfb4f7537369b9fbbcee3a045dccab2aca644bff3b8f2379f2b383ee968643bea3c07773d91a8aa4fe61eb98f3b19ccd9b9e6916ccfbea380ea34d20858a3b804eba8ee4dfd0da1b5e8c5357ae63d8e594c9e636a271a6eb98f043012a894968739dfae639e2af45433c4a12b48eb98e9abe324a64128220679e23ddc754b1fba39fe4eae788f2deb12bbfc8e7d06ef8de3deb093d60bf29e9e8ce788e865af6116e8677ed778e23bc4394caf5109d582e) (by decide+kernel)

private theorem block10:WideCovered band 10938351 11606748:=PRB band Z1.f1327 10938351 11606748 (WB 240727514264 16 0x81fc7181a37bd0a7f6235b903f8ea0c06f63b63ac1deb5ffd1d65bf19e4f3ed7ea3f3ffa3985f637a6e9caf314f7ff470f1b1824f7f75d1c42fbd8f0861cdbe1a6ab7abc9f7b1e0a9520c4f44d6a3e1bef63a9cc34128cc8aca4947dec7036937ea634f5802caf7c8efdee0de05fdaad78d9ef91e26fa1f7a302d55d83bdf23b0f0f3d5dfb4aa17d879e4760478718f06752e954f7c8e32c2cfa8d94aa345edef91ed42966ebff0d417263cee3b97103d6b6c0a78b1d) (by decide+kernel)

private theorem block11:WideCovered band 11606749 12275147:=PRB band Z1.f1328 11606749 12275147 (WB 240761068632 16 0x83023ec4ff427a98eed372e0c08fbd01904a8b3baaa9c83023eb815405410ee81db60c08f9b338fc90cbb9643e83023e26263e6f57ee304420bf8f75a9cf75253b81de182fe3d6ce83cca88eddeaca03f8f3e9d0f19d57b6d78380fe3c57dd3b81c4ed8d15203f8efb084ee32afb5912580fe3b0d473c3452ed3b7da0bf8e86bacf24223b44ac782fe3a246bc085ebace9e6203f8ee1c74da978db304697efa3af9ed3345fd2c984ea03f8e6b684d1f808b1be0b) (by decide+kernel)

private theorem block12:WideCovered band 12275148 12817520:=PRB band Z1.f1329 12275148 12817520 (WB 240761136216 10 0x8c6e3c4959d782c5cf0e51c22b08ff40dffca79d2c250cf8ade3ad6f98d1fb7e70429c61418e891c313a6074bfc41385063a221104cb16b2fc83921418e831d212aad58be7db5850239f99984924322f76a1e1408e798ad11eb28cbd3758830239ce8a445c4d72f250a60c08e6e2fa1118408bbf0fa) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7471033 12817520:=(_Q1 band 7471033 7638132 12817520 block0 (_Q1 band 7638133 7805232 12817520 block1 (_Q1 band 7805233 7972332 12817520 block2 (_Q1 band 7972333 8181206 12817520 block3 (_Q1 band 8181207 8515405 12817520 block4 (_Q1 band 8515406 8849604 12817520 block5 (_Q1 band 8849605 9183804 12817520 block6 (_Q1 band 9183805 9601553 12817520 block7 (_Q1 band 9601554 10269951 12817520 block8 (_Q1 band 10269952 10938350 12817520 block9 (_Q1 band 10938351 11606748 12817520 block10 (_Q1 band 11606749 12275147 12817520 block11 block12))))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 14)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:14≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤57)
    (hT0:2905≤T) (hT1:T≤3284) (hnu:7471033≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤41467633654348955:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAN
namespace CYF
open AI AP AN
noncomputable section








open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CYF
namespace DAD
open AI AP AN
noncomputable section
def band:Band:=⟨15,39,4017,4125,42555913051436406⟩

private theorem block0:WideCovered band 5111754 8653001:=PRB band Z1.f1330 5111754 8653001 (WB 206366661720 38 0x2ebb6d5da2390f7708119375db694ad1a78a783c236baedb39ee8bc25dc1bdd15d6ed9589455613e0cd43aeb76c61ba24614705dcf56dbb60e110fd60382a7e7b6ddaf3fc86b0cdc130a9db6ed6e00426f75e086b02db76b11220ddc4f03a8596dbb6280504117b818d99b6ddb078880e80bc0a382db6ed7e2e400a0de0401cadb76bc1f9fcf1bf0173bd6dbb5c354fc076780734bb6cdad3e47d1cc1c0165bd966d61543de4e5dff9892cb36ac879eb2bdeff3f21659b53f90f380577f58fdb2cda889e782bd9bf8934d966d4ecb3b7887dfb2f56cb36b1b61d84eb6fd0a83659b57700ea3fcf7e3eaeb2cdab11a746bebbefc0d5966d527d39c4b8df6c61ecb36add61e5f7a4fad5e7659b554e4f1cbde7d2460b2cda9c307848e73e6ee65966d46233bd3189f25ce2cb369e929dbed54f8a149657b4cb58ec8c5e7c0a11aebda4dac7583413de1bed75ed189a3a575e9edf3aabaf683aa9cf067cf66cad5d7b404f8e562c67aefc3aebda8b46719bef3d5497d75ed3f7c387ece9e98a6c17f600de803ac72f4380e083b0031000a470714994) (by decide+kernel)

private theorem block1:WideCovered band 8653002 9231164:=PRB band Z1.f1331 8653002 9231164 (WB 206366695480 22 0xcb0daa19b409ea3a336cf32c369738cfba6348c4e15cb0d9fb513d11e422f03b71c3655db4eb62788b33c6c70d823a1bb6e22a2a9a7f1c36901e8dce7928a1978c6fda0bf83660c3a2631471bf671d64da60aa88ff2ac6fd9447737064a221c80f1bf6078bed0a74587e4dcbefd9eb7a28524421d5ed2fbf6791089ff96a871121befd9dcba27a99521b2a36fbf674d3c9cccea8683fabeed9caef26dacf218f59afbb6701e899794485f6d3baed9b6e625ffc1216c0feebb66b26c967bbc8569abbaed99fa02511bea148c5eebb664cd89295ec84dc84baed9a9f5243238a1257c2ebb66c7c08f49d0844f5d) (by decide+kernel)

private theorem block2:WideCovered band 9231165 9736525:=PRB band Z1.f1332 9231165 9736525 (WB 206366695512 14 0x35b36dfc7581a5794a48a6eb56d8923b1b6daa940638d6ada17046406bbd26f223ad5b0d9e7cd43bda4bafab4bf625c95342982c92f61e97ed6009a5ce64991d19ccf0dbd644542a7f12288eb9dfb748f6a411cc242dd3b3bf6d81113b4334481513657ed88f025bd88c8f9cffcafdac4dd49dc9d91e1fb1961b485cc8bd76823a0ac72c36be6150bd63846fac56586d65afa097f288d6863) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5111754 9736525:=(_Q1 band 5111754 8653001 9736525 block0 (_Q1 band 8653002 9231164 9736525 block1 block2))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤39)
    (hT0:4017≤T) (hT1:T≤4125) (hnu:5111754≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤42555913051436406:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAD
namespace CYQ
open AI AP AN
noncomputable section










open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CYQ
namespace CZL
open AI AP AN
noncomputable section
def band:Band:=⟨15,41,3839,4075,30833963291952495⟩

private theorem block0:WideCovered band 5373896 8087454:=PRB band Z1.f1333 5373896 8087454 (WB 206366693495 31 0x575f126fd2be9089ed9e7abaf8915a95dbc54f63f055d7c47838ae136a7ad766aebe231ea56a13f3d47a5575f112b0ab01539e91cbebab8862f1563854f3fe27555c414f0aa272e79b6f8aaae1f8b25453613cb76e55570f59429e0009e49b06aab882b254c7734f1bd4b555c4532ea4f4a2789689aaae2209851fb913c2736d55710be9a8ced99e0194aaab89a09978f0cbef7c6d553c4b706bb6581f7761ba69e25f985fdd88bb96ffd34f127102f88be5db97929a78902d178ce6aed3b914d3c4e58eba7d557655aca69e278425c9e5cbb06c8534f138052e1cd95d715d69a78999cd6ee162eafab34d3c4b776b64d6975353ea69e24ffb5a8dacba769151471217f2cf5da5d2941e8a388d1e564fa32e8b9d7451c4481eb107017414d0056e003df00e3ee79e65a0227001348040781c62f5c1078009940201e0da143c083c004b600fecc6406ac) (by decide+kernel)

private theorem block1:WideCovered band 8087455 8401266:=PRB band Z1.f697 8087455 8401266 (WB 206366693432 17 0xb6de29eb766f341803172b6de2915466641b7fe957b6ce269dc6210c47fa13bb6ce2599d6174a07f591fb2ce2473260d0027f1103b2ce231fd601f907ec8e8b2ce23e0a5f02c67e80ccb2ce26dab5e25267e38b1b2ce26f4b5da0a87df095b2ce263f95cfc327da87ab2ce259005c85027d605eb2ce24cf05c0ab87d1843b2ce23f855b8b3a7cd027aebe22ed85ac4b87c880caebe21d8e5a321a7c3ff0aebe2098e59942c7bf7d5aebe2101958e8387bafb9) (by decide+kernel)

private theorem block2:WideCovered band 8401267 8991972:=PRB band Z1.f1334 8401267 8991972 (WB 206366694488 31 0x31c38c0af139582f8934e4c2fe3404d3fa1baa2292b6fbf8cb858fc772e885c91befe317673e5caca2051d6fbf8c0584f7297e87cc5abefe2e8dc3d30aaa1e10fafbf8c4228f221e2873c23befe32ee43bde6fa1bd01efbf8c8bc0ee00d686abecbefe316383b2085a198f42fbf8c1a08ea5a96861bb5befe2f7c63a312ca174e66fbb8b9f18e72452858b7ebaee2d63a395d7fa150d8aebb8b0130e2ea3e84fb47baee2aa5c3840f8a12ccaeebb8a49d0defbba846b10baee2ca8037327ea108bd2ebb8b8214da940283dad8baee2d546365717a0e4af2ebb8b24d8d82102834aa1baee2bc2435b784a0c0a16ebb8aafb0d4f85282ba6abade29c1934e60fa09c93adb78a29dcd228e6822a33b6de30bb33fa6b8207885edb78c2edcfb4c848199fcb6de3782640ce9c6054782db78da8490145998109c5b6de337ac3d40d720306a6db78ca13cf30c4880798e) (by decide+kernel)

private theorem block3:WideCovered band 8991973 9582678:=PRB band Z1.f1335 8991973 9582678 (WB 206366727288 17 0xcf2e261a335f34f8923856cf2e20c6eb3b64f091a81fcf2e28e39b25a8109117e7cf2e26b21b13cec89087b0cf1e24998b0beed88ff779cf1e2162daf9c5488f6742cf1e1d9a0af4c8c88ed70bcb1e16e45ae0ae208e46d4cb1e0a8a6ae2c3208db69dcb1e0e2fc2c3a1108d2666cb1e1d8682a65de48c962ecb1e1a4ffaa990b08c05f7cb1e1487d2aa15238b75c0cb1e07c83a9cc0528ae589cb1e26e8f69062318a5552c30e1bff820dfc3089c51bc30e1b907a0a4158897d00) (by decide+kernel)

private theorem block4:WideCovered band 9582679 10098995:=PRB band Z1.f1336 9582679 10098995 (WB 206366761016 14 0xdefe1bd4555d45339a1933d72e231db5577008998b22d72e1feb3d41c73a98faebd72e21785535fc2a986ab4d72e1fa9ad29a74a97da7dd71e1e3741215954974a46d71e1c47b115468096ba0fd31e1a9eb10d3cf69629d8d32e184c29008a209599a0d32e17ad3cf7c9e2950969d32e18f1f4ef5658947932d32e17c25ce9849893e8fbd32e1671f0e3c0a49358c4cf2e14c278dc326a92c88d) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5373896 10098995:=(_Q1 band 5373896 8087454 10098995 block0 (_Q1 band 8087455 8401266 10098995 block1 (_Q1 band 8401267 8991972 10098995 block2 (_Q1 band 8991973 9582678 10098995 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤41)
    (hT0:3839≤T) (hT1:T≤4075) (hnu:5373896≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤30833963291952495:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZL
namespace DAM
open AI AP AN
noncomputable section
def band:Band:=⟨15,42,3755,4049,31088676933195465⟩

private theorem block0:WideCovered band 5504967 7836912:=PRB band Z1.f1337 5504967 7836912 (WB 206366693495 27 0x55573365b263e86bde53c2aab997ce130b0bdee9821555cc9d2a9755caf70331aa9e63d094b4e257b5d28d34f31450257540bd9c5ca9a798d1f929186dec51254d3cc9632938edaf5dfb3a69e669394937797acb69d34f32f572469dbbd537d29a79950ad222f15ea0a294d3cc90f89081def4bc35a69e63a3347cd5b7a39aad3473159f23bbe8bd0a9d68a39b30956a006ce7c32b451cde352b36cd27398b6a28e706d35903a739a7eb514737d752c36249cc1bde8a39bbd895fd53ce57c2f451cdc27cae945e727538a27e6d36456c67139162c4f3f36206ab1dfa9c78de679f9ac44155bf6ce335333cfcd5d38a99a467151ba05be404cb00e0a4f8846d0327202610070495c1dc6c18390082c0139f1dea738083c80420009bcc6637aa) (by decide+kernel)

private theorem block1:WideCovered band 7836913 8135401:=PRB band Z1.f702 7836913 8135401 (WB 206366693399 16 0xb2be67adb54df45f08ba6baf997f0d5098efbda09aebe6530f53a2d1ee44aabaf99af2d4c484fb484aaebe6a80a520d9bebfdaebaf9a8be146c277ab68baebe69670515e97e9b6b2baf9a1c15436f5fa24ccaebe6773c508185e76fb6baf99950d408f079930daaae64ec44f864fe528baaab98d8e53c5b7f9014eaaae63f6a4e9cade2e1baaab99b27d371c0f86f8eaaae684d84d3a43e09abeaab99e74533ac777ddcf) (by decide+kernel)

private theorem block2:WideCovered band 8135402 8433890:=PRB band Z1.f702 8135402 8433890 (WB 206366693400 16 0xb6de70db75db3df0161c56dbce0d96ba82d201a00adb79be31d73680400f91db6f373b52e1a7c7fd643b6de6d6175bc598ff1ac96dbcd851eb6a611fd1212db39aa83d6a4aebf7dd2d967348012d07827eb2c5b2ce6713659824afcd3cd659cd2d2ab111fdf8841acb39af0715f4353eec13d96736912ab94507d8f47b2ce6c3c756a962fa8ccf659cd6a4aac9765f3f61ecb39a8c1156ce83e5a5459673482aaaa5ef7c6bc8) (by decide+kernel)

private theorem block3:WideCovered band 8433891 8937590:=PRB band Z1.f1338 8433891 8937590 (WB 206366727288 27 0xc2fe5d99d9d0b1b8886076befe5ccfe1cc01a0881797befe5c09f9c89b7087ceb7befe5b2cd9c515b88785d8befe5d9a79dc6046873cf8befe5fbc21d6169686f419befe5e89c1c94fe586ab39befe5e0769c63e5d866259befe5c4cd1b19178861979befe5bc7d1af353085d09abefe5b2241ab8f288587babeee5a8159a90718853edbbaee5ea9f9f08a6284f5fbbaee5d9899eac55a84ad1cbaee6954da6d72d484643cbaee69f522672bac841b5dbaee6b829a82b0fb83d27dbaee6aa12a7bb21b83899ebaee5ec229d4a7ca8340bebaee5e3429d2377282f7dfbade6115da039d7182aeffb6de6037c9fec369826620bade57c8a18763a8821d40bade570ba185259081d460b6de561cf98164c0818b80b6de5523d17ebf888142a1b6de5623417bdd8880f9c1) (by decide+kernel)

private theorem block4:WideCovered band 8937591 9534568:=PRB band Z1.f1339 8937591 9534568 (WB 206366761048 19 0x679728c91c5d40ea245f1a33cb93a69a2d210d121d5539e5c9c203966fa309058eacf2e5410e8ad507047e395e7972919ac55802c23cd5af3cb93e6bc2a872711d47599e5c966b4157d6148e11edcf2e4080acae59a446c017658f20cfb64cf8b1e33b9bf2c798e36f517657518b961963cbbd3527b8b428bcaf1cb1e55c9114ac677459c99658f214f19a6bb0062a9dcb0c393e7b51e698f1142b67861ca08280f107c889ccd4c30e4ff9f4777fee44c1fa618727dc9a3b6324224ec570c393db951d77c2911e46b861c9e3c48e9e75088a956) (by decide+kernel)

private theorem block5:WideCovered band 9534569 10131546:=PRB band Z1.f702 9534569 10131546 (WB 206366760984 16 0xdb2e68ab092e5ecb3530b5b65ccc71aa43b24a681a6f5cb9904ad4622aeccba6e6b9f30a04285b49b98e31dd73e62a278fe031130a2bbae7cc2cbf9f1ed1a5efe7b5cf97eec73c599d4b96efeb9f2ef82274e76b969c20d73e5c5a18e547db2c14c3a67cb42031bab64a55e28b4cf95d0d3352e55ca7371e99f2d754466b7c1945524d32e59d0c8ca739d2786c9a65cb0a9598bc7fa4cc6974cb95a3df304d42494ff369972a554c5fbe01920e27) (by decide+kernel)

private theorem block6:WideCovered band 10131547 10280230:=PRB band Z1.f702 10131547 10280230 (WB 206366760984 4 0xdb3e6fbd3968dbcf39ba4db67cd8b8daaf2ad671365f6cf9b65795252244dddec6d9f35907c9dcf789b2a19) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5504967 10280230:=(_Q1 band 5504967 7836912 10280230 block0 (_Q1 band 7836913 8135401 10280230 block1 (_Q1 band 8135402 8433890 10280230 block2 (_Q1 band 8433891 8937590 10280230 block3 (_Q1 band 8937591 9534568 10280230 block4 (_Q1 band 9534569 10131546 10280230 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤42)
    (hT0:3755≤T) (hT1:T≤4049) (hnu:5504967≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤31088676933195465:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAM
namespace DBD
open AI AP AN
noncomputable section
def band:Band:=⟨15,43,3675,4023,32307587669057266⟩

private theorem block0:WideCovered band 5636038 7615452:=PRB band Z1.f1340 5636038 7615452 (WB 206366693495 23 0x534f535b4a137289d0cf729a7a9624908b3b4e7d4714d1d4823e837cf673a095a28ea4364416ec539ab78d14752713208b619cc353a8a3a9775102c8d4e58755451d4fe30801986727a07a28ea73c03fd5cb391831d1475338a9fce769c79afe8a3a95ea0fd0e14e33a37451d48e7e7e042e715378a27ea34e93ebc253884ea4f3f51e611f37f39c300c679fa946ecf7c8e4e0ed1b3cfd4c5d87b1b1a702cea9e7ea68d83d3c7b37f1a34f3f52eea9e787a9be668e79fa94a24f2e174de9fff3cfd48bbc78f9ea6f065c05ce81297031f92f75e5c029f402d6006eb35b8a5c416fa00e0001f4c9da05c4083d004e40099d06868a9) (by decide+kernel)

private theorem block1:WideCovered band 7615453 7917076:=PRB band Z1.f706 7615453 7917076 (WB 206366693399 16 0xaebea5b1e490475e33852aaba9516121c9ef88470aaaea5f05481085e0eb36aaba9be351e81af7f129aaaeaa93146b6ddde9e1aaabaa8d4519a6a775de2aaaea92e5462c8fdc50feaabaa005117b4a76ca9baaaea68a7457ed1da03e2aaba93ad114d2d763754aa9ea41ca44e515d7b6c69a7a96a811145875a40da69ea6bc843e4b1d569aa9a7aa16f50d8d9f510c6a69ea8b564306c3d31c8e9a7a9ef1d0ab2c747d7f) (by decide+kernel)

private theorem block2:WideCovered band 7917077 8218701:=PRB band Z1.f706 7917077 8218701 (WB 206366693399 16 0xb2ceab675500f29f5a136cb3ab67893d9c4fd1ea9b2ceaee2a4ed927f3541acb3ab6469398edfc8b62b2ceac2ed4e1af1f106fecb3aaa46d374237bf81bb2cea885e4d441feeb9e2cafa98c5933afc7b64d4aebea62c44c8d51ec6cc2bafa9b871308e4fad18caebeaa0dc4b40bbea1fa6bafab24dd2a517fa3e45aebeabe3f4a4a73e7d28abafaaa6b12776d79aafeaebea93b5499845e5856ebafa9e7cd2541a7917b7) (by decide+kernel)

private theorem block3:WideCovered band 8218702 8520326:=PRB band Z1.f706 8218702 8520326 (WB 206366693400 16 0xbaeeb312058add504050d75dd62794b00cd606e38aeb7abd16d5e71ec0b79fdd6f56784ab974581259bb6deaa8ae56b97901b7f16dbd5a69eaba2d2024952db7abb74154cf2402458db6f58ab22a3cb27fff0db6deb219653baceff6ad36dbd61b68a6d561fdaf16db7abdc514c68cbf91115b6f56e75a963ec7ed87eb6deabbcd522db6fd1db76d9d52d6ea39d69f914decb3a9e80d45a7ebefdca596754fd5a84da47db1f0) (by decide+kernel)

private theorem block4:WideCovered band 8520327 8953911:=PRB band Z1.f707 8520327 8953911 (WB 206366726264 23 0x1861d4033167cb6222280df0c3a7dbb6ce78fc442b4a617f50ffe5c41964880cf0befea1167b8288690f869b7dfd446407668cca1de6a6fbfa8a9f8e9ef494398035f7f5286f9cd93ba86e662befea4ec9b954b850d397f7dfd4bc1576b82ee194c6efbfa94914eb9c15c304bc5f7f5168fdc0739285bfd4befea218ab7c39e50aec6375dd4a37e7ae5a2614b236ebba8fdbaf35bdcc271755f774d4e2578b848849946beee9998f2ed60f1089f4575dd30d015d23e621017faebba61cbeb8589441de2ddd774ca4096e04b88372b7baee9a6a6ad6099106522975dd371d359fd8c20b7dc2ebba6ba6ab2d4d8414ae6dd774d2211643250824c29) (by decide+kernel)

private theorem block5:WideCovered band 8953912 9557161:=PRB band Z1.f1341 8953912 9557161 (WB 206366727288 19 0xd33ea70b6a7df5f991d4a9d33ea06a227fd231914162d32e9369427843e990ae1bd33e8e3d3e969831901ad4d33ea2e2c6836ff68f878dcf2ea1292a2bc6dd8ef446cf2e9a72d228d31d8e60ffcf2e8d717229b51d8dcdb8cf2e820a01ffa5048d3a70cb1e9cca21b410338ca729cb1e9974f1b549238c13e2cb1e937361b322f38b809bcb1e8ac0aa3cde5a8aed54c30e9f6969b45b918a5a0dc30e9e46f9b0f2c98a106ac30ea615b9d9430089c6c6c30ea5c779d53df0897d23c30ea53151d2bb2889337fc30ea47621ceea6088e9db) (by decide+kernel)

private theorem block6:WideCovered band 9557162 10160411:=PRB band Z1.f706 9557162 10160411 (WB 206366759960 16 0xdb4ea66a25d5eed26c246f6d3a9245e71d3c69a75d4db4ea2bcd1ba3226678a376d3a839616bbac0994f46d74e9e88219fa5ce62efff5d3a70cf6655ea79828b8d74e9f2cf185a7065e55c75cfa781f56007b997022ad73e9c71b576f6ee59bb8b5cfa6a8b05b729695db9bd73e98c1d96890825521534cfa57ba9578ab794b50dd33e929039592a8e50871b4cfa6400c52ef72938e7fd33e97c99149aa4a4bece34cfa57dcf5116099267f1) (by decide+kernel)

private theorem block7:WideCovered band 10160412 10461465:=PRB band Z1.f706 10160412 10461465 (WB 206366760984 8 0xdf4eb324a9427e273f4233be9d67a0e26800327c40337d3ac454b49cab34f3e62ef9f57543a8e412e9de97edf3eac285511ddd13aac6fb69d52a6d20b96be730bc36d3a9b8d83f4930ce17d4eda75367ee7854969b9c62) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5636038 10461465:=(_Q1 band 5636038 7615452 10461465 block0 (_Q1 band 7615453 7917076 10461465 block1 (_Q1 band 7917077 8218701 10461465 block2 (_Q1 band 8218702 8520326 10461465 block3 (_Q1 band 8520327 8953911 10461465 block4 (_Q1 band 8953912 9557161 10461465 block5 (_Q1 band 9557162 10160411 10461465 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤43)
    (hT0:3675≤T) (hT1:T≤4023) (hnu:5636038≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤32307587669057266:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBD
namespace CYG
open AI AP AN
noncomputable section
def band:Band:=⟨15,44,3598,3997,32830673985121336⟩

private theorem block0:WideCovered band 5767109 7462341:=PRB band Z1.f1342 5767109 7462341 (WB 206366692471 23 0xa28ee93ab79b34271ddc5a28ee9823790ad671935da28ee85bd78b2427148f6a28ee6efc7814f270fe8ea28ee5a5f77adf270b427a28ee5bf37735b27069bf9e7ee682a766efa701f589e7ee6f3575dae66fd4f09e7ee8c6174b9ba6f8a889e7ee92397419de6f40209e7ee83e073c16e6ef5b99e7ee726973315a6eab519e7ee5f7772cb9e6e60ea9a6ee8a49751535ee16829a6ee92d0747be9edcc1b9a6eea730738d3ded81b39a6eea7d8730d61ed374c9a6ee9c3e728c41ecece49a6ee9056722cf1eca27d9a6ee81fe719ca5ec5815055ec153d062a156c0dae04cec0b6b033148ebc34605bec040100f6c06a99a7) (by decide+kernel)

private theorem block1:WideCovered band 7462342 7767102:=PRB band Z1.f710 7462342 7767102 (WB 206366693399 16 0xaaaeeabfe426a27da10faaabba3ec909058f639d6aaaee6ba441e81fd7bdbeaabb93b4906e89f5a507aaaee4771418bcdd56a82aa7b958f10447c751038a69ee556340cfd7d317469a7b965510202d747b69a69eea10a3f8277d0c4069a7ba627cfcfb873e699a69ee7f643f016dce70ca9a7b984dcfaf607351caa69ee543c3e8b0bcc1d8e9a3b98078f883df2bcfba28ee62983dddcdc9ca528a3b9a454f63f1f2282c) (by decide+kernel)

private theorem block2:WideCovered band 7767103 8071862:=PRB band Z1.f710 7767103 8071862 (WB 206366693399 16 0xb2cee7b6a4959edecaadacb3b8fca524ebcfae04eb2cee45ae48c58bea579ecb3b8c391229b37a4b7fb2bee475e480693e80462bafb8da5d1f5b979b6b0aebee1f3647b081e5b126bafbafe2517810f921e1aebee9e8745b955e35deabafb9d8491651a788d12aebee4d7e453033e10aaebafb90461141f6f7f843aebee320944e34fdeb772babb9187911483f76374aaaee3de9441779dc6436aabb9fc890c8d2f6cea5) (by decide+kernel)

private theorem block3:WideCovered band 8071863 8376623:=PRB band Z1.f710 8071863 8376623 (WB 206366693399 16 0xbadee8018513e17ff44bedb7baab79416f2ff86c7b6deea85050028ffcf182db7bac7e13e327fef1f8b6def0d604e2b31fa9e46db7bb9e0138000fe5d29b6deeb91e4ddaa9f84b0adb7b9eedd359317dc85ab6dee563a4d41e5f5f7cadb7b98ba132cc07d338ab6cee4d6d4c8e43f3a48edb3b8bf6d31db77c9ebbb2cee6e104b7135f15152cb3b9d75d2c09b7c09ecb2ceed4fd49deedeefe16cb3baaf4125f717b751d) (by decide+kernel)

private theorem block4:WideCovered band 8376624 8681384:=PRB band Z1.f710 8376624 8681384 (WB 206366693400 16 0xbefef93b658b78b08ef517dfded68ab0419a10b502fbfbcfa7d5f57f41f16cdf777824fab9591839871beeeeeafd56d7a7069c1575dddcac2ad07c60c0e8aebbbc3e7556617415c9ddd7778d40aa8e64826ed3baeef319554867f0448d775dded99aa6c0e207680eebbbd35214ca23c0c7ce5d7779400a97a27814534baeeef7ef5272ab01f59b75ddd7f86a47d0602c196ebbba7fdd46a224032ff5d6f7490528b7e1801b96) (by decide+kernel)

private theorem block5:WideCovered band 8681385 9271857:=PRB band Z1.f1343 8681385 9271857 (WB 206366727320 27 0x6797687138d4b5ae635e8c72c7b899526c0d35119cac5963dbdf2c35e3fb88c5093cb1ed98ef1afff7c45dde2638f7380e0db4d89e2c9bd71c3b985066d0562f15b91d861dc9d623600b578a9226c30ee3c109ad505bc523dfe187778030fae315227f55f0c3bbd0607c70fe91365e1861dd64573989b26896888c30eea5a39c8eeb3448f10e18775c2f8ed63116234ee70c3baa54475c804b1112a585fdd53583bbbea4883eeabefee96c99d9848243fa41df7f76b22507841ce1ea86efbfbb0b988249b070ebf697dfdf022a48da12287154cbefef72ef2428db14365725f7f7b08791e2920a1a01f2fbfbd450a8e001650c6c2b7dfde7a5f462fa0285ebadbefef2af522d032142d0a35d777fac815e417c6155b7aebbbf4e4cac717830a18ef7dfdbb3912c7fd6084c20f) (by decide+kernel)

private theorem block6:WideCovered band 9271858 9881379:=PRB band Z1.f1344 9271858 9881379 (WB 206366727256 16 0xd74efc6812a0e41f2d8e47ae9df3c08538174e58c9535d3bd8bcca44b81cacec2eba778c1d1433a9f9508b6d73eeb1b7a7bb23728e7cdae7dc3f4c4fdc0fe4f7c5f5cfb421f49e29cbc9a5246b9f63dbb53c5b5792b579d33ee9a0aa2b9cab244155a67dca6e3477d71a462f6f4cfb6e1c28f2ed1487b86699f630d3513b4d590623dcf2edc8349e6b1691f9adb9e5dc53f33b371b23ce27b3cbb74c3275e45c4751e7e79769ccc4ebe1208e0f00) (by decide+kernel)

private theorem block7:WideCovered band 9881380 10490900:=PRB band Z1.f710 9881380 10490900 (WB 206366760984 16 0xdf4ef3bd9d142d9f402829bebde0783a0eae527dfd177d7bb79703ef5804f753b6faf77833479e2209e55a7df5eecd46cebfdd73b81b1bebdd51c89c89b7e74b0277d7ba27a637cb4b4e4b9d6daf73017c6bb8499c026bdb5ee314f4cf63f736db39b6bdcb79f18f01de6b63376d7b91c31312102cd21ff6da77156ee5fe7e099af2fdb4ee0b688bb0d553234bfb69dbda8a970ffbe6216435d3b704482ce209cbf860eba76cebfe5705e8975bf2) (by decide+kernel)

private theorem block8:WideCovered band 10490901 10642700:=PRB band Z1.f710 10490901 10642700 (WB 206366793752 4 0xe35ee009c8a1d033a2650ce35edea3ca9c5bdca1d281e35edcefb0957c60a13db2e34edb9408909404a0a8e3) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5767109 10642700:=(_Q1 band 5767109 7462341 10642700 block0 (_Q1 band 7462342 7767102 10642700 block1 (_Q1 band 7767103 8071862 10642700 block2 (_Q1 band 8071863 8376623 10642700 block3 (_Q1 band 8376624 8681384 10642700 block4 (_Q1 band 8681385 9271857 10642700 block5 (_Q1 band 9271858 9881379 10642700 block6 (_Q1 band 9881380 10490900 10642700 block7 block8))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤44)
    (hT0:3598≤T) (hT1:T≤3997) (hnu:5767109≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤32830673985121336:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYG
namespace DBA
open AI AP AN
noncomputable section
def band:Band:=⟨15,45,3512,3971,33760984407698038⟩

private theorem block0:WideCovered band 5898180 7264472:=PRB band Z1.f1345 5898180 7264472 (WB 1305878321271 24 0xcf47916149b9f519bb63613cfe4913e6d50826e8dac4f3f92df71b1ac79b90a053cfe4e81c6b60866df7554f3f936291ac7519b6b0a93cfe4ddea6a8fea6d60fe4f3f9354c1a8eb39b457493cfe4cf0a69dabe6ccaa64d3793bfc9a3f669b1fded2cbe75a70898df6ec344f4b2f9de36a2233abafa49134de4fd2a67450e6b9df84d3793e5a19b1ff9ad4b352cbe5cc626d1589eb07a14b2f97afc9b116a7aaf1d92cbe5db326bf2f9ea714a4b2f9706e9ae0d47a8987d2cbe5a56c6b0cd1e9daf34b2f9641a1aad9c7a63f21249e599ae6a2fade9449c4927969b29a67257a3e5c40b3e00eca01aded68ae4502cf8024c003cb03a05fb8083e006680094ac636535) (by decide+kernel)

private theorem block1:WideCovered band 7264473 7572368:=PRB band Z1.f1346 7264473 7572368 (WB 1306952062071 16 0x52a7cbc029fd153bce2e414a9f2d6f97eff76f3406452a7c99bb1c9c0f9cbd4e54a9f25714736ed972aa0d52a7c91689cd2445c97b894a9f2306c732ce97213b652a7c85325cc9305c7222d4a9f1e804743551f17d5fd1a3c6fb41cfc753c4c8d3468f1a83872f6ed70e70850a3c9df55bb0f35c26f75428f268196f38d8f050b150a3c959bdbf0651c01619428f248a26f92b06fba5a50a3c92651bbe141bdbcbd428f23baa6ebbb06f2403) (by decide+kernel)

private theorem block2:WideCovered band 7572369 7880265:=PRB band Z1.f1347 7572369 7880265 (WB 1305878321207 16 0x575f96e94a3274f783e49575f96edea2f6f577f31d575f9627422efb077a7f257579668422b320775cc655579739ea260be77119b5557998c521d97c76c66f55579963ba1b385767b435557983dca18ed2763017555796fbf21674875e4ec555797050213bab7599c0555796922a12c54754e95554f96cb620f6f17503695557918521dc451f4b83e5557906f29dc758f46d12d3578ec8f9dda25f421e7534f988271ff62773d6bb) (by decide+kernel)

private theorem block3:WideCovered band 7880266 8188161:=PRB band Z1.f706 7880266 8188161 (WB 206366693399 16 0xb6cf2f6be4e218bf3c406cb3cc262535eb8fca5d5b2cf3432d4c7d2ff16aaacb3ce31bd2d514fc0f7eb2cf3666e4b3c1def114ecb3ccd58d2b9f47b7927b2cf2fb584a8defecb7f2cb3cb85052a098fae2d0b2cf2de554a201dea5e96cafcb834126b687a4c79aebf2eea3491dcbe8053abafcb1c512482079b622aebf309d14816fde5abdebafcd1ef11c263f91fcbaebf31d7146ba93e35282bafcbb1611a92f788974) (by decide+kernel)

private theorem block4:WideCovered band 8188162 8496058:=PRB band Z1.f1347 8188162 8496058 (WB 1305878321208 16 0xdd77918e8262f2cc0d1dd2ebbcf669554195205623975de7443aa92089021ac6baef2e0da49592b80c2375d7794d74a4a720c03b862ebbc9d799254c6600af8175de4d2c091fb4effc168baef22deb4929357f95885b6f9e317a86f713fa52eadb7cf67c94139f9fbfcc56dbe7643e9fe34cfd680cb6df382cb4f90e87e68da5b6f9a64f27bd8f3f0ed7adb7cc57253c5471f74a0d6dbe62a9a9d4a98fb0eb0b6cf31a474e258c7d3c2c) (by decide+kernel)

private theorem block5:WideCovered band 8496059 8803955:=PRB band Z1.f1348 8496059 8803955 (WB 206366693464 16 0xc30f35eac55264bc32b39e18798582aa671fe182d1f0c3cb6b9952615f0b8039861e55442a943778574f0c30f2632054d6dbc294e2e187927b02a3330e137a670c3c6b5755525570926db861e27786a9e959844841beff3710c4efda041fe8b5f7f99d8ba7706520ec7aafbfcbde353b3d0906cd7f7dfe5448c9d99a0831b93beff262174fcff94168345f7f9182aa7c83a60a14f2fbfc826193b90910474237dfe3b8889d68a881eee5) (by decide+kernel)

private theorem block6:WideCovered band 8803956 9362017:=PRB band Z1.f1349 8803956 9362017 (WB 206366793848 25 0x67978a0c4c3d96e998eda61cf2f0fc6707c6b6331c88159e5e0c0b30f54094636b6cf3cbc98e0de9b7c4fc68bae638f85f8d91bcffae8c8105c71f0c19c23735ecd186bb58e3e18d5cc7276ff62faabb1c7c30b108e357c6c5cfc1e38f8663ff1e289fc8b5457c70f0c75903bcc1a9161259861e1836587684c922af8030c3c2edbb8eacb8645396ae187866b541f1229b8a27a9c30f0d4f403d6286713b8fd861e1ebbbc89cc4aa26454b0c3c3c62711183ad44a3136187867c2a1dde0b388fafac30f0cb3e43b4bdd7115f9f85fe1c3ba8851348a21928efbfc36c95106d3b1440cbc5f7f86fb282221da187ce4cbeff0d7ec043a0fb30f0643861e0ef19c56716a21cdfd70c3c1e96e8aade2c4376656187839eb8155182086a19e) (by decide+kernel)

private theorem block7:WideCovered band 9362018 9977810:=PRB band Z1.f1350 9362018 9977810 (WB 206366760088 16 0xdb5f1cb18d3077e2260ff4b6d7c689b14bab1b897a97bdb4f16193128fffa25c4c936d3c400184a62de8967ccdd74f1027b924795625799db6d3c2106f4a491a895501fd74f16e4c511f21de52e7235d3c4cdab44de796942371d74f0b855d033f9964e346b5d3c1573d411fc7592f6c3d33f115b754a449924981af4cfc673704ea051491ca14d33f14f2ad3c6cece44cef74cfc2b53a4cce292909d66d33f0356472dc5546401c3f3cbcb65947bb97408f70b8) (by decide+kernel)

private theorem block8:WideCovered band 9977811 10593603:=PRB band Z1.f714 9977811 10593603 (WB 206366759960 16 0xe36f3441c1c96f7a86950f8dbcc79056eb108a10eece36f2f76a1ac48aa81e2578dbcb589168800a9fe23edf6f2aae3d9376ce7d2f9f7dbca0ce5624b539eb590df6f29a86179930e787ce77dbca372f5caf6b9d88e2df5f26fe21699a3e73ca2f7d7c93cba5817649c5c34df5f2306795a9b0e6f17736d7c815745437719b2f85db5f1d70a54b053e6a64bb6d7c866944fdda09a02d7db5f20d0bd3be12665b2036d7c7bcdb4d8d6898d629) (by decide+kernel)

private theorem block9:WideCovered band 10593604 10823935:=PRB band Z1.f714 10593604 10823935 (WB 206366793752 6 0xe76f2160808ff390a528ffe76f20142c8be1f2a494f6e75f1e69f0865d94a3fe9fe35f1c9d46806b79a36848e36f1b1aa67c022aa2d1f1e36f1934d0762824a23b9a) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5898180 10823935:=(_Q1 band 5898180 7264472 10823935 block0 (_Q1 band 7264473 7572368 10823935 block1 (_Q1 band 7572369 7880265 10823935 block2 (_Q1 band 7880266 8188161 10823935 block3 (_Q1 band 8188162 8496058 10823935 block4 (_Q1 band 8496059 8803955 10823935 block5 (_Q1 band 8803956 9362017 10823935 block6 (_Q1 band 9362018 9977810 10823935 block7 (_Q1 band 9977811 10593603 10823935 block8 block9)))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤45)
    (hT0:3512≤T) (hT1:T≤3971) (hnu:5898180≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤33760984407698038:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBA
namespace CYK
open AI AP AN
noncomputable section
def band:Band:=⟨15,46,3417,3944,40441970920258437⟩

private theorem block0:WideCovered band 6029251 7137304:=PRB band Z1.f1351 6029251 7137304 (WB 1306952095895 31 0x264ded04bc4de73c9b3a0613a7f5393a18ee2cbd938519b37a970a0c74bb5ec5039cd9bd47e4063a5baf60224e6cdea3faa317b9d7aee16b366f5111d18bf58bd6d8d59937a90384c45215eb207b4c9bd54d76602b9ef56a45a64dea94fe308f655aa2271326f542d01874f89d479589937a9cf78c3bbb469f0bd4893d77c687641b9f4d266a449ebc10b3adce8fa56379224f5f2f01ddb4e6d219dc9127afd0e4ed085b68c0ff4893d76992702231743a87a449eba8e337e0baba0a481224f64650a28e064cfba60911fb1e89d1311ea679141468fd8dca0888f0133a2a8a347ec7b7d43c17099be5891a3f6462da198134cd5ae48d1fb23b550b3fe2666183468fd901d284e6e5330ac9a347ec720642130a997268d1a3f6311fa0d8c04cafb660517a021a0034ca1e531c4027bd00a7c00ee40b272ea0137e8053d00770c39137d40a2f401d20024880c63c6e040fa00ea401237060bebb) (by decide+kernel)

private theorem block1:WideCovered band 7137305 7448337:=PRB band Z1.f1352 7137305 7448337 (WB 206366726167 16 0xa28f6b86dac3f45e34e23451ed49f85803a9c56c8679fda434eae6773887994f3fb4fdf55938df0c3429e7f6ae86aabe14e0eea73cfed87aa548855c0ad8e79fdae590a7e3d77efba4f3fb55c8d4d76aef93849e7f69e06a97b6cde8f293cfed1a265252d5bbee9269bd9e7d4a34587757dacd37b3fc85438bfee63c59a6f686a0282aa2dc2fad34ded32be4f6b61b72f9a69bda63329d8e8b6bffbcd37b46b5d39156ed3407) (by decide+kernel)

private theorem block2:WideCovered band 7448338 7759369:=PRB band Z1.f1352 7448338 7759369 (WB 206366726167 16 0xaa9f6ec2ab3524ceccc134d3edc2c7657a95d868669a7dba8c4c9765bae715534fb868258d152f5823aa69f7254f30f76aea6c974d3ee273b6132edd3a96e9a7dc09fac177afa4f36534fb765817fbdc74527ca69f6d3f8af8a8be80d1b4d1ed74a75e894bceea768a3dad498bb17ff9b7575147b6577171bcbf322bea28f6e9a22d9333e5ad9f451edd87a5a84e7ca2b7e8a3db72e0b3c25b91f785147b65c9964d4371f300) (by decide+kernel)

private theorem block3:WideCovered band 7759370 8070402:=PRB band Z1.f1352 7759370 8070402 (WB 206366726167 16 0xaebf786fe3c66e3f64a055d7ef8cd3768381eb644abafdee9cceab263d4691d75fbd3025d2fc67a4133aebf78b92b9d6a0f3ea895d7eedbdf728cede6a552bafdd30e6e2b3cfcaeb2d757b94b55c28c7791175aaaf71057b7a033f18b0b555ee62db6db123e1e656aabdd7e08d7cd0bc16d35557bb56c9abd9a77e1b6aaaf75675350e06ef2b8f555ee7fcc6937dbdd275eaabdca720d15cafb7ef45557b869859ece176b1f8) (by decide+kernel)

private theorem block4:WideCovered band 8070403 8381434:=PRB band Z1.f1352 8070403 8381434 (WB 206366759959 16 0xb6df649b7d23745fff1fd5b6fb1d6f290b26bfe602adb7d89d7f477272fe98376d9ec231f233f777f002bb2cf5fc01117b2b3f5a1e5967af02bc89b1bff9a132cb3d7ed8243a72dfc38bb659ec3f9ba12543fdd06db2cf61c4090741b7ec23f5967b078ba825bcbf4e23acb3d802e04085f1f9d93f659ebe1aa1feb5cfca0afb2cf5e176cfdbe23e2a60595fae6a327d5e6bf02342bafd6d7743ddf23f779c35d7eb5e7a9ea7c67b70f1) (by decide+kernel)

private theorem block5:WideCovered band 8381435 8692467:=PRB band Z1.f1352 8381435 8692467 (WB 206366759960 16 0xbaef6ba0b9706d8e128bceebbdaa6df5a1ea4845703baef6c5c51630b52102c52ebbdb78505704b483bf24baef6cccd5579b6a0dccd6ebbdaef7c54ec3e832745baef6aac89502f2e0b6d5aebbda582352de00828f66badf67f84d4696ca090ddaeb7d9aaed50e2f681f786b6df64f3513e3e9606ae5edb7d8bfe44e23ad815fa7b6df6531053259de044ee2db7d9ad484b896480c7c8b6df6691b52a295e01ef66db7d967fe49b689802fe9) (by decide+kernel)

private theorem block6:WideCovered band 8692468 9139575:=PRB band Z1.f1353 8692468 9139575 (WB 206366760056 23 0x638faed9cc769bfb62dd5df1c7d740713adf2cb165311861ebfeeb20d983c8add98c30f5efe690474ca4548d4e187af2d1a80643d22916e70c3d7bcde3f8c54913f395861ed8394a9ae8ca89addac30f6b332149c50544b0f5e187b3d66699500ee2457ef0c3d9ae8d4bc75b711941985fed054b27d008a887e1cc2ff67037d3a9955441916df7fbb9c36e015fc21f98f6fbfdd28d16d374810f349d8e3e9525e9445cb9874e5ebeff7803d1a273c0438137df7fbb5398cdf82a21ad9fefbfdd629065e7aa10cd5217dfee8281b221588861ea0beff728c118a5f9042e958df77b876e4c1c8582161b06fbbdbe13c5fc75610a75a575dedb516aefdce084eee2) (by decide+kernel)

private theorem block7:WideCovered band 9139576 9761640:=PRB band Z1.f1354 9139576 9761640 (WB 206366828664 18 0xd74f48ec240abb807a53cda35d3d1e846c2a3a106945b89d74f45bb650aaf72fa4f0eab5d3d0c4cf02ac84ae932bcbd74f4245b88b37dcda4a4fb34cfd1d3ab4247935d91fc0dd33f461c4c091603f64590bb3cbdebf3d8ea36d3c90cc4fcf2f7dfbe3401fc4ae40d1c33cbdeedd9906a3f828f9c91cf2f7472433f955baa3c12cb3cbd97efb4de62a628e6cd3cf2f579c6f3b4ec04a3753d33cbd6a61eae0993ba8d3d15c71f47ea6207a913263294db1c7d1f97f41e608f98c5947c71f48df4d0894de4230355f1c7d22aa9421f0ab08bc167) (by decide+kernel)

private theorem block8:WideCovered band 9761641 10383705:=PRB band Z1.f1355 9761641 10383705 (WB 206366760024 16 0xdf6f67e8415568379e7159df6f6508654f9cc79dd97adf6f670e3944f9ab9d419bdf6f676fd13cf30f9ca9bcdf6f656f0537241b9c11dddf6f6379353499079b79fedf6f60a1012f13479ae21fdf5f5ce72d296d479a4a40db5f58004528f41799b261db5f57fac123c32f991a82db5f59215d1dbde79882a3db5f5cfbb514ed1f97eac4db5f594f651137d69752e5db5f53f5a111064296bb06db5f4a23390b9261962327db5f432dad096984958b48) (by decide+kernel)

private theorem block9:WideCovered band 10383706 11005170:=PRB band Z1.f728 10383706 11005170 (WB 206366793752 16 0xeb7f67af4891e7fda7ecf2eb6f65d4a48cb8bca7576be76f639b4a864c62a6bf8ce77f61c7b6818dd5a627ade77f5f86ac7b6c01a58fcee77f5fe01075a756a4f7efe77f5e70e271c127a46010e77f5d42b86ef626a3c831e77f5bc5f66b3813a33052e37f5a386a677d6ca29873e37f58d84e64dc31a20094e37f5856a461042da168b5e37f58a3a85df853a0d0d6e37f5791045b9cc4a038f7e36f56a1125a17829fa118e36f55600257c1359f0939) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6029251 11005170:=(_Q1 band 6029251 7137304 11005170 block0 (_Q1 band 7137305 7448337 11005170 block1 (_Q1 band 7448338 7759369 11005170 block2 (_Q1 band 7759370 8070402 11005170 block3 (_Q1 band 8070403 8381434 11005170 block4 (_Q1 band 8381435 8692467 11005170 block5 (_Q1 band 8692468 9139575 11005170 block6 (_Q1 band 9139576 9761640 11005170 block7 (_Q1 band 9761641 10383705 11005170 block8 block9)))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤46)
    (hT0:3417≤T) (hT1:T≤3944) (hnu:6029251≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤40441970920258437:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYK
namespace DDP
open AI AP AN
noncomputable section
def band:Band:=⟨15,47,3350,3916,38257049879827671⟩

private theorem block0:WideCovered band 6160322 6985014:=PRB band Z1.f1356 6160322 6985014 (WB 1306952062103 27 0x952fdb39a34738b3aa54d92a5fb6b8d684c0e752441a54bf6ebaacf1f9ce9fbcf4a97edc5599c0e39d35e38952fdb2afb340513a589a12a5fb6383661e3e748adaa54bf6c4fecb6904e8c9014893ed8b2d950239d0f89c9127db286325f773a0be69224fb6a26642b7673f1732449f7cc16de92cc6796324893ef6f71baffa8ce92fe8d1fdf4c7377e76f9bf32d1a3fbeece6e57fdf3580c2347f79fded594e3666364468fef6445a83e56cc2d628d1fdea3734d2f0d9727f51a3fbc7826933e1b2bea56349f5419aa8d8dae53096c693ea4549563a74c9c7c78f1fd40262af57c7925cbf1e3fa72d855cc0cb2253e63c7f4c912ab434963fdc8c78fe9b835543432c7622a8d1fd3af92a555c58d9184093f8090401a100718bd70123f012040341a862cafa) (by decide+kernel)

private theorem block1:WideCovered band 6985015 7299182:=PRB band Z1.f706 6985015 7299182 (WB 1306952061975 16 0x50a3ecf3a9cd0f4dec0dd9f3fd98f1396785bc4eed3a7fb321a72151376383a74ff6dbece0624ee7a544e9fedb325be2e7dc5b409d3fdb2efb797afb783b53a7fb5f396ecd236ca1ca74ff6b27edcc486d47864e9bed8561b6381d9f5a49937db20836756fb2b87d326fb6d926c23df630b5a64df6f748d67926c14b84c9beda39dab8c1d790089937db258354231aded45326fb679e69e2875974ea64bf6ccbad2d856ae1ea) (by decide+kernel)

private theorem block2:WideCovered band 7299183 7613351:=PRB band Z1.f1357 7299183 7613351 (WB 1306952095863 16 0xd3a7e5724a7db7ee742ba7d3a7e4eedc7f3280f3def4d3a7e44fcc7dfcae73924050a3ea65daa3d0f6f3458d52a7e6bfbe77d6ce72f8d952a7e690be79c9f5f2ac2652a7e658bc7a5dd5725f7252a7e64e8c79ab487212bf52a7e6150e79784c71c60bd1a3e5cc6e795698717957d1a3e563e67964e0712ca3d1a3e48f887a355070dff050a3e6c8ce73a410f0933c50a3e6c1fa745f5070468950a3e6aa707407406ff9d550a3e6923273a9786fad22) (by decide+kernel)

private theorem block3:WideCovered band 7613352 7927519:=PRB band Z1.f1358 7613352 7927519 (WB 206366726231 16 0xaeafadf503033a5bc7b6fd557d6ae057f438de2a8b2aabebab9ebd4226f0baf1555f5e8d25dddc97810c5aaafb218aae1d50bbe208d75fcc6435094819dddd7abafe5d5f284931cee5555555f5daf75a8c6176ddf7aaafad0a5ace305bb48a1d557d58e99653735d912429a7eac826b0ca0eebefb9555f36c873f0c6c75ab29aaaf9ab759f77483aaf3ad557cccc20febb93d4470aaabe61c6a7f50ede98a1d555f2f4833ec14074785b) (by decide+kernel)

private theorem block4:WideCovered band 7927520 8241687:=PRB band Z1.f1359 7927520 8241687 (WB 1306952095831 16 0x5ab7e75de0975cdefb842eb56fce14f12e97d5f5d5916adf9a744a5da56be94582d5bf32d754a7da0fcdbfd5ab7e5b77a97366af91e93b367ca79812a2e33f10a5962cfb3f5ab4d87e3dfaf12c57f62d1569057c7ba92f56afec80dccf6a08f6b8f6ad5fd943619b8c31ec3f2162cf9bbe4a31b837d618a2c59f34f01463172fa766158b3e630f48c865df4535aad5fda03918b0069e773e95abfb23b430f1c03cc8232b57f60be8616102794393) (by decide+kernel)

private theorem block5:WideCovered band 8241688 8555855:=PRB band Z1.f1360 8241688 8555855 (WB 1306952095864 16 0x5ebfe814e4ac78fe4146a7af5ff3cfed562efd20902717aef9e11d2acb01903e7d0b977cea7e5544acc81a735ddbbe55c90acce6e40ad40ae5df478a851eb15604373972efa13b4a8fca89018234b977cf419d4792f48074675cbbe7887aa2c5e64013d9ae5df38be05167331ff6c0172ef99e1a28caf38ff1c98b977cb0c2947f3537f4199dabbe50018a185a53f7a72ad59f70b3973dc605faa0c96adfa12b225609d0fcb6fcb56fcf70952a69c07e0ecb) (by decide+kernel)

private theorem block6:WideCovered band 8555856 8870024:=PRB band Z1.f706 8555856 8870024 (WB 206366726168 16 0xc30fae5762f5568875888c30fac351aeee50870bd5c30fa9e402eb43d86bf21c2ffa8be32e79a986726ec2ffa86b02e3da58625babeffa81b1ae000385d907beffa7d692dbf48858c53beffa9f1fad0a4b853fa0beffaafc4ac978d84f2ecbeffaba782c2c8d84a638beffa9f53ac074b845984beffa7f422be437840cd1beffa5880abc42083c01dbeffa394b2b6e1483736abeffa2b882b4da48326b6beffa1aa02b326482da03) (by decide+kernel)

private theorem block7:WideCovered band 8870025 9459090:=PRB band Z1.f1361 8870025 9459090 (WB 206366793848 25 0x6797dd22e46e95a31905592cf2fb54a3ed67e0731f78579e5f5ef375a3be5063c8b133cbe9e78fb4258fcc744aee797ccece96b91b798deff5c71f9007b83e408191aad1d8e3f2074247abdd9234276f1c7e4fb24113dabdc65e93e38fc9c5692224af38c7074c71f93242e4399f271847818e3f256f6885cf9ae2f5c371c7e49590109cb8dc5c52ce38fc8ed5620dd4cb8b3da6c70f9154ca40fc5b715e1e5861f218480806d26e2a90ff0c3e567e893fb569452bc5e187cb33bd274aea28a0ad8c30f965c304d4f485137c49861f2bd8309918baa25c5c70c3e66225166cad0c4925ee187cc77ca2c5826988d80ac2ff982bc857333431116ad85ff2efc84ac5392620fa8f0c3e317ea0bf085c43f8f7e187c600b217c5be087a53c) (by decide+kernel)

private theorem block8:WideCovered band 9459091 10087427:=PRB band Z1.f1362 9459091 10087427 (WB 206366827640 16 0xdf6f861ee410473e64cf601efb7c23876082405d2654a737dbe112dd03c3ab8731726bbedf05bee21e5c373981fced75f8a47d1179e9614bc3336ba7c5644a0b79cc8a5bb3ff5d3e2e8f10586c6552ca731ae9f15ebbc2bc120295ba31d74f89f29315606994a90656ba7c4618c8aa0c2ca521d8f5d3e1ba6d4553a47527dbf9ae9f08935629e6fca935495d74f81a8fe964165d495d97679fd0dc1923b76bc248871f4cfe1ba0a447d58c32310c19e7f2708c478b56a890eef9) (by decide+kernel)

private theorem block9:WideCovered band 10087428 10715763:=PRB band Z1.f737 10087428 10715763 (WB 206366759960 16 0xe78fb122d559b49e8e09cf9dfebd08754dd97a2e90ce77facd26d4a7aca893e978dfeaa2af511cb2a1b63ee37fa776f13b069a84735f8dfea09ec4d305ba08370e37fa960552bf2ce7fa8278dfe9f0894a25569f50a2e37fa58e6d22e75a7adcef8dfe8bf9a475c589e1dd4e36fa01b851a7a527611b77dbe75c2f451b939ceb06df6f9c45bd12aae671467f7dbe7927442dddd9bb838df6f9b77e90bdd3a6c7b477dbe725cd4158279a856a) (by decide+kernel)

private theorem block10:WideCovered band 10715764 11186405:=PRB band Z1.f737 10715764 11186405 (WB 206366793752 12 0xef8fa65fa6819fd9aab0e5ef7fa48d3c7d01a0aa19e0eb8fa2bd52789155a98079eb8fa08edc730666a8e712eb8fa01fbe6ec38fa84dabeb8f9f73e26abebea7b444eb8f9e4180680b3ea71addeb8f9cc886648daba68176e78f9b843661fce0a5e80fe78f99ea4c5e8462a54ea8e78f9929ee5b17c3a4b541e78f99a3a258ae3ea41bda) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6160322 11186405:=(_Q1 band 6160322 6985014 11186405 block0 (_Q1 band 6985015 7299182 11186405 block1 (_Q1 band 7299183 7613351 11186405 block2 (_Q1 band 7613352 7927519 11186405 block3 (_Q1 band 7927520 8241687 11186405 block4 (_Q1 band 8241688 8555855 11186405 block5 (_Q1 band 8555856 8870024 11186405 block6 (_Q1 band 8870025 9459090 11186405 block7 (_Q1 band 9459091 10087427 11186405 block8 (_Q1 band 10087428 10715763 11186405 block9 block10))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤47)
    (hT0:3350≤T) (hT1:T≤3916) (hnu:6160322≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤38257049879827671:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDP
namespace DAE
open AI AP AN
noncomputable section
def band:Band:=⟨15,48,3285,3888,44081636532876497⟩

private theorem block0:WideCovered band 6291393 6866507:=PRB band Z1.f1363 6291393 6866507 (WB 206366760055 17 0x924fd2aae079925268c64b924fd2ee9878772e6878d3924fd2bc8c77f876682b5c924fd2709077550a67dde4924fd21d5c76a88e67906d924fd1e8c87623526742f58e3fd1fd0875611266f57e8e3fd207a074c7b666a806924fea2df9684f11665a8f924ff8c36d7ec0f5e60d17924fee89815130b1657228924fe2ba81231c6564d7398e3fce69d8be6e75643c4a8e3fd6068890537963a15b8e3fd3885086ed48e3066c8a2fda2998a370c8626b7d8a2fd415d486321861359f) (by decide+kernel)

private theorem block1:WideCovered band 6866508 7183811:=PRB band Z1.f771 6866508 7183811 (WB 206366726167 16 0x9a6fe7c0ba1a5e7db3b8734dfd044342cf5bb5412e69bfa0bc6847e536816a4d37f3b7ed07f6f6cb55c9a6fe685020cb67d8cfcb34dfcbb4a4128b3b069b6697f975e481b1e75e67b4b2ff313b5015fbeb7f7e965fe65049ffb65d6640f2cbfcded83f5617ab923e597f9b0ae7dca6754b8c4b2ff310a0fa999ea49a0965fe55d09f2438d3f8532cbfc97363e02bda6bac6493f939b47b309f4b09d4927f295acf490f6913c2) (by decide+kernel)

private theorem block2:WideCovered band 7183812 7501115:=PRB band Z1.f771 7183812 7501115 (WB 206366726167 16 0xa28fea87a25d161e4ea77451fd86974a8addc89f0e8a3faceae9489cb8ed265147f50145272fdf18cd4a28fe8bb7a4c017e27ebb451fcfd9348f74dc3c79689ffa0f5690c087852374f3ff41fc11fee97056f69e7fe9004239e51e012ff3cffd2e3746b26dbef01e79ffa6b928c077b7b7484f3ff45801165d6ef21189e7fe7a9c22a726dda7433cffcdb8144d447ba18a679bf9b3268901fb71c594d37f395b90fc08edeb3a) (by decide+kernel)

private theorem block3:WideCovered band 7501116 7818420:=PRB band Z1.f771 7501116 7818420 (WB 206366726167 16 0xaaaff10d92abf42ee9969555fdf9af54dee5dbfcf2aabfb8f32a907d7b58e2d557f625194fc4d76644daaafeaebba9a1e3ec2dad555fd52ea52e60bd7257a9a7facda0a42703abdf3d34ff5efd1452b8f52e6fa69fecc8da83b83e9c1f14d3fdbfdb4f6081d24e029a7fb32469e2e3fa2304d34ff5a0913a381f3f891a69fe978f26fd25e756334d3fd23954da2f7cd76868a3fa61ca99e7f7988155147f4be393220af2c2b2) (by decide+kernel)

private theorem block4:WideCovered band 7818421 8135724:=PRB band Z1.f771 7818421 8135724 (WB 206366726167 16 0xb2cff53e9314d31f84859659fe5edf622d9def5ad2cb3fc10d8c283a7dc49ed95ff7eb81832f8fb3bc5aebff0cceafd86cf5dc9d5d7fe4d915e616bea835abaffcc118bb335fd29afd75ffa743170812fa05e7aebff36cf2de53df370e15d7fe30c65b1d57e5abe2baffbd3b2b4c8f3c8ec0d75ff6706568164f8d009aeafed21dac9819f105255d5fd98b758c4a7e0d46aaabfb77d6af6bd7bf3d1d557f7ebf1598ff779a2b) (by decide+kernel)

private theorem block5:WideCovered band 8135725 8453028:=PRB band Z1.f771 8135725 8453028 (WB 206366758936 16 0xb6dfde23f5cdbecc07dd25b6fef97fee3605a02b8b2db7f7ed107095e700c16b6dbfc1a38375c1180133db6dfe0107db8cf93fe2e35b6fef8c14da81e9fde13adb7f780376c4312fe55af6dbfb9c96b5dbe47edd5fb6dfdb7299aa8463f47f45b67ed1ae2d41b9df909c2cb3f6b0a268c864fbe9f3659fb73adb3a93d7da781b2cfdbeb8199d713ead055967eeb102c938d9f4324acb3f72968643534f97e37659fb7679b1b6657c71a3) (by decide+kernel)

private theorem block6:WideCovered band 8453029 8770332:=PRB band Z1.f771 8453029 8770332 (WB 206366759960 16 0xbeffe92c0912e03a174c72fbffa011243ec348585a4beffe6c26d0c660214e0b6fbbf9644b42946384eab5baefe406b506c4e21274faebbf89f204122c9844fc6baefe2d37500879a10093eebbf90e1e3f068383b4d7baefe51a38f91d1a0d9d82ebbf93d183d846f8319e8baefe4260cf4aae20b31c6ebbf8c7313c903b827ef9baefe1f7b0efc15208c60aebbf835ff3b923d81e40abadfdf6270eb8efe065a4edb7f7776f3a7f0981491b) (by decide+kernel)

private theorem block7:WideCovered band 8770333 9186794:=PRB band Z1.f1364 8770333 9186794 (WB 206366793848 21 0x638fea3ac8215027c8c2deac71fd40606420179917c0e78e3fa71e5c82c0a922e4bef1c7f4c3e2902f0b245a2c26187eabe4924edee38af80cc30fd4c93248fe1c715552b861fb874c4bc2636a2974770c3f74dcb16fd3394507d36187f79d504a4a74189c22ec30fedd9969198c5312e96f861fb09e589e43982249cff0c3f5f1ee139a8ec446ce46187eb8d1826a8e68888c50c2ffd675ae4c79c21107db37dffab6bbc96e0ca21fc586fbff5368b128eecc43d1f55f7fea038224b6208875672beffd4ac0448155f10e11f57dffab0b948d7ed221aee0afbff5627d917e960433705df7fea8483229adc8862093) (by decide+kernel)

private theorem block8:WideCovered band 9186795 9821402:=PRB band Z1.f1365 9186795 9821402 (WB 206366827608 18 0xd34ff06112556559295dcdad34fe6d66148ef37e9541ebd33fe3a9f6418e11294a6fcd33fe4e1743d43352940c0dd33fe1f7bb3a711ce93711ed33fdefaa938009ba92d62fd33fda7e45339f3de923b40cf3fd66d0331a257a91a051cf3fd09551300876a910562cf3fc61a942f19ed2906a73cf3fc6cf25b1639628fcf84cf2fd3d2be28700c68f3495cf2fd0e35428d354a8e99a6cf2fce968434d69258dfeb7c71fca018f11842788d63c8c71fca3e6111426248d1651c71fca894a10fc97c8cc8d9c71fca6f8a10cf6908c7b62) (by decide+kernel)

private theorem block9:WideCovered band 9821403 10456011:=PRB band Z1.f1366 9821403 10456011 (WB 206366861432 16 0xe37fc440ab8448c86b3f1797c6ff88334b08849e767bc3738dff118a341091736cf2af6f1bfe20e39020bbf7d9dbafee37fc3b6b3041c297b3a401fc6ff86218c08331d367214838dff07dcc6107f81acdf518f1bfe09db78202ff2c9b4f42df6fc2005e03bab0373568a7b6bf9d9b5d184bebea68658f6d7f3638742dccda14cbf3a6ba7f0dedb8e9011b998e385d74feb476c220aa62130912dae9fca175f3b5d5a825eb69f5d3f809770697aea84b895c6ba7edfa02cbd2e1e09677c9) (by decide+kernel)

private theorem block10:WideCovered band 10456012 11090619:=PRB band Z1.f748 10456012 11090619 (WB 206366759960 16 0xef9ffe29fd9307e2a4eaefae7feaeca612988a89fcceb9ff7af597a05f6a01377ae7fe5e285adc77a769eeeb9ff726c1620ffe9b3bffae3fd4a4456e1f5a63410eb8ff29cb1525e3e9664879e3fbf6bd52482da4fe32e78fed40fd42f0ba918d0f9e3fb310a4e4edda3c854e78fee1849300ef68cb5979e3fb1c754b1e2ca29276e78fea3d5926b5ce87de1f9e3f9edae483b4da15c98e77fe51bf91e2aa28306a78dff8551f4618e5a026ba) (by decide+kernel)

private theorem block11:WideCovered band 11090620 11367640:=PRB band Z1.f748 11090620 11367640 (WB 206366793752 7 0xf38fe9f8e88337d1ad74d8ef9fe7e4be7e59ddacdc55ef9fe56f26786a05ac4166ef9fe3652a73e0d5aba677ef9fe3b94e6efab3ab0b88ef9fe2191c6b30e4aa7099ef9fe0be7e686198a9d5aa) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6291393 11367640:=(_Q1 band 6291393 6866507 11367640 block0 (_Q1 band 6866508 7183811 11367640 block1 (_Q1 band 7183812 7501115 11367640 block2 (_Q1 band 7501116 7818420 11367640 block3 (_Q1 band 7818421 8135724 11367640 block4 (_Q1 band 8135725 8453028 11367640 block5 (_Q1 band 8453029 8770332 11367640 block6 (_Q1 band 8770333 9186794 11367640 block7 (_Q1 band 9186795 9821402 11367640 block8 (_Q1 band 9821403 10456011 11367640 block9 (_Q1 band 10456012 11090619 11367640 block10 block11)))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤48)
    (hT0:3285≤T) (hT1:T≤3888) (hnu:6291393≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤44081636532876497:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAE
namespace CYB
open AI AP AN
noncomputable section
def band:Band:=⟨15,49,3223,3860,43084007545634496⟩

private theorem block0:WideCovered band 6422464 6843042:=PRB band Z1.f1367 6422464 6843042 (WB 1306953178199 16 0x4a9601d8910c51b3da1aa892a58075df231066f681c66c99201d3aa0c378059f38ad224807546e308aef677fef489201d9d18c092fd9cc6d122480775502fd92b66e378489201dbda8be9b8d9a54f522481b7b18a5e968e647014892061cac24e71d397e319224815a354855fa465aa8a489204cc411f706d195713d224812f6808b42c0e50e134892030b511ddd4b391c67122480219cb82731863d525468e029d459083d438ce2b91a38092c503eb968629c37) (by decide+kernel)

private theorem block1:WideCovered band 6843043 7163482:=PRB band Z1.f1368 6843043 7163482 (WB 1306953110615 16 0x4e9e072f64d34fedb539693a781c4f935a7caed001ecc9e06f626d66421b2c78f36681acc835998e6c63a7cd9a06972ed54cd9b055b3366818c1eb56a226bc730cd9a0652e8d3e021ade3d532681dc03b3984e6b2ab94c9a075426cdfff1ab71f932681d1d2b3435c6a8e42cb96073b46cc1099a9001f2e581c886b2db1669f1cb4a960729a0c9e541a68e412a581c69f323d6c6955544a96077b8ec67809a41c652a581dcd4b167e268b8dd) (by decide+kernel)

private theorem block2:WideCovered band 7163483 7483922:=PRB band Z1.f780 7163483 7483922 (WB 206367774743 16 0xa28819c4714e666723212a2881a1f614ad8671e3d6a288195abd4827171959ba2881890054658471475fa28817a4394473070f924a278179f7d4120c70aae89e7817b57d3ec9e705cad9e7817e6213c27cf00e719e78183fed391b56fc0369e7818dbad3484b6f71fa9e78184b6932f43ef23bf9e7817a87d315286ed5839e7816dbd92eae9ee87489e7816ba652cc676e390c9a6816cc512ab576dead19a681739e927348ed9c95) (by decide+kernel)

private theorem block3:WideCovered band 7483923 7804362:=PRB band Z1.f780 7483923 7804362 (WB 206367774743 16 0xaaa81dcad983a4af715caaaa81cb80180043f6c78eaaa81b9a797dcc8767953aaa81a47f97b821762b17aa9819c96d770d4f5dcdca69819d61d7435ef58ea0a6981a007171100f54065a6981a63b56d59974f229a6981c27d5656caf4a3eea6981b6615639377455b2a6981a88d961b21740777a698196cf95e56173b93ba6981860895c2ad736b00a688185b7159db1731cc4a28818d18955be0f2ce89a28819343d523a1f2804d) (by decide+kernel)

private theorem block4:WideCovered band 7804363 8124802:=PRB band Z1.f780 7804363 8124802 (WB 206367807511 16 0xb2c8108246e5fb1fdfcc1596407d5227220f9eead1acae03b2ceb89ea4f6ba175d701e96e5bdaa47b0ecfaeb80f82eadc7f23d604a575c07f39d6ce027e9c962bae04270d3593eef4483b5d70207ce1a7c4b79d5e1aeb80fb48cd2a0fbcc3d3575c078a7068ae7be4e5aabae0390e0b3bb7df1d65f5d701b4ad59af0d789cf3aea80da64ccbe8bbc275c555406f41064bffde001f2aaa039d16319450ef648355501e019d86ec2776405) (by decide+kernel)

private theorem block5:WideCovered band 8124803 8445242:=PRB band Z1.f780 8124803 8445242 (WB 206367808536 16 0xb6d8141e5c8b246901ba756db02977c112239e023bfadb6056d70217c07402061db6c0a97ce4274b37ff287b6d8149cd083e3f2ff48996db027f3ad05bc91fd5842db604c94ba0458ebf83eadb6c0928263ffd357eb999b6c81156207ed480fcd6bd6590222834f95361f8748acb20456c41ecfab3ee773d96408e4783cd4587d80abb2c812804e77be38fa64e1659024f054ebed39f390d2cb2047b529d4c28be4afcd96408a7ee3a35137c47bd) (by decide+kernel)

private theorem block6:WideCovered band 8445243 8765682:=PRB band Z1.f1369 8445243 8765682 (WB 1306953178232 16 0x60c2029469969a9e285c0f260c20287b496795728572b660c20252951691ab285247b60c202389816797b284d63fdec20217d7966495a848804dfbe01485c16f41f58439c85ebe02af1594f6e4983eb8d5ebe02881e953bd14839d515ebe025892151b41b834f165ebe023a1d95457328300da5ebe021f5e14e8e5182b29f5ebe01fe0614e24218264635ebe01cf2594e6d318216285cb605607ba457b9881c7ec5ab60520e5a3f2bf08179b15ab604ebcca340f68812b75) (by decide+kernel)

private theorem block7:WideCovered band 8765683 9146205:=PRB band Z1.f1370 8765683 9146205 (WB 206367841368 19 0x31c603003a529b0ab8b8f5dc7080bb27c49b394e2d048b0c20324da1415fde8af2e6c3080c16e04ef0a7a2a92af0c204c2121cd1ce18a566fc30813514b70d2e062820d31c601a52dcc47ec489b9f8c70806717c30b896225aef31c201956b0c2427c891d80c308065ec6301d442233d170c2019cc7cbe6c5c888109c30806595e2f6ca9220cb3b0c201a4d5cbaeef487e492c30806b3672e1d4021e595f0c2019d9c0b8183487481bc3080628312dc31121be7830c201748f8b6d4b486aba4c30805796c2d72b021975a70c20159ea4b4b754860f2d) (by decide+kernel)

private theorem block8:WideCovered band 9146206 9787085:=PRB band Z1.f1371 9146206 9787085 (WB 206367910040 19 0x6ba401796da154e39a2555b375d200a949a0aa195112974adae9004602f055bd418941ddfd748014bdc02aabef449c0b46ba4006d2c413963f1e4b93c74ce01402421246598d2490f59e7021777ea156a24591ac03cf380d4ca250ecc1124887c6679408843826db963ce41cc573ca03ebbee356d8c871fad3d9e501ac7fd98ec0ed38f3a27cf280ab5b68bb87231c74ed867940424bd46ca8dfce3804e71c600a79e408aca9a51ac9858e300558d50441e4a28d1687c71803176ac24a1268c66425e38c01845de12265e0631e8431c600e27e30aa53fc11857a98e3006e35d053e26308bdd99) (by decide+kernel)

private theorem block9:WideCovered band 9787086 10427965:=PRB band Z1.f1372 9787086 10427965 (WB 206367841400 16 0xe7880579eb3d36f2b3e3c7bcf100799827b6ac727a071b9e20105d80eb421dcef2a7f1bc02c3c91b562629d48d8df68137e9579cc7b13958c3b6d0246c00eb83e62703fab6da041f179befe684db9b9f1bc01d2211de52219ad6fcdb5810e24267f720134750bb6b0201968cb9946266783b6d603b9e1d8970004c80cbedac06e764b02c3c0986520db580c71085e768412f9153aeb0152852b97f3425cb0cb5d602885dd6d13044b47ddeba4063bdaab0bcf095f344) (by decide+kernel)

private theorem block10:WideCovered band 10427966 11068845:=PRB band Z1.f759 10427966 11068845 (WB 206367808536 16 0xef9819e1be9ef70551cb5bdf303189d537bf92a124dbae605d5a2a5dee753d65ff5cc0b48a74a2f3ba71048eb981780d68f9e394ce7a3d7302d9d291b301a975d6bae6057021a2b047529d71f5cc0a5f27448313a49e6ceb88136162862b094803ebcf1023dab90937d68d95fb9e20475d72064db516483f3c408ce884011eea22c90e788127be87c9035432033cf1022dcb4f8204283ce8b9e203fa559eaa73d02b95f3c40704bc3d82139fbab4) (by decide+kernel)

private theorem block11:WideCovered band 11068846 11548875:=PRB band Z1.f759 11068846 11548875 (WB 206367841304 12 0xf3a813e1777440e2b038cbf3a812e2c06ff71daf9ecaf3a811e3816bcefeaf0253f3a811ea976700dfae65dcf3a8113fc6643e1eadc965f3a81074d060d986ad2ceef3a80fc73c5e40ccac9077efa80ef4b25af528abf400efa80e39a6586efbab5789efa80e475f557003aabb12efa80e0cbd534145aa1e9bef980d8e8751a4eaa98224) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6422464 11548875:=(_Q1 band 6422464 6843042 11548875 block0 (_Q1 band 6843043 7163482 11548875 block1 (_Q1 band 7163483 7483922 11548875 block2 (_Q1 band 7483923 7804362 11548875 block3 (_Q1 band 7804363 8124802 11548875 block4 (_Q1 band 8124803 8445242 11548875 block5 (_Q1 band 8445243 8765682 11548875 block6 (_Q1 band 8765683 9146205 11548875 block7 (_Q1 band 9146206 9787085 11548875 block8 (_Q1 band 9787086 10427965 11548875 block9 (_Q1 band 10427966 11068845 11548875 block10 block11)))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤49)
    (hT0:3223≤T) (hT1:T≤3860) (hnu:6422464≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤43084007545634496:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYB
namespace DCV
open AI AP AN
noncomputable section
def band:Band:=⟨15,50,3163,3825,44229008218871759⟩

private theorem block0:WideCovered band 6553535 6917557:=PRB band Z1.f1373 6553535 6917557 (WB 206367877207 16 0x96582236a601b09a7b4c6dacb2c1119c040d72bd5a4fada596088c1fe06b3112d1df6d2cb044617e035440d68a0b79248222ef201a834bb428dbc92411191b40d27435a00ae2492088ce660689446cf67712490446966033e7036764b99248222ba6819d846b38adcc9241114b380ce037d9b1aea492088a5800666d62ccef752cb079c4b6c8a1e6ae628bb924825f996046899032ecddc92412a8334205115b962af24920957fea11fc5a0ca7779249047935a07dfce6649dbd) (by decide+kernel)

private theorem block1:WideCovered band 6917558 7241133:=PRB band Z1.f762 6917558 7241133 (WB 206367773719 16 0x9e7830e981e2c65dcfb5b3cf06432abb4493b8baba79e0c789d7632536efd74f3c18d37aebb6bed90af9e78319d9dd456bda835f3cf062cdbba5413b3cac269a0c61ed739d1f651d84d3418bbfae5dc06c54b19a68321531c4f48d80b6334d063a6e3871b9aedaca69a0c72177041275b3d94d3418d2e8dfb24eb18b39a6831ab8dbc545d593672cb0632de374761a9ead25960c63236df573515da4b2c18f104d974de9dcb5) (by decide+kernel)

private theorem block2:WideCovered band 7241134 7564709:=PRB band Z1.f1374 7241134 7564709 (WB 1306953144407 16 0x52a60e508b56136cf36da552a60e45a05540f6f31ea652a60c78ea419ff372cfa652a60c587941f78c7280a752a60c47b8419a847231a752a60c1597419eae71e2a8d1a20c0632412bd47193a8d1a20bb49d415ce67144a950a20e229950109af0f5a950a20e077e4f5d56f0a6aa50a20c77373e76107057aa50a20c6e2c3e1c147008ab50a20c55043dfb886fb9ab50a20c506c3d8b946f6aaccf9e0c35093d633e6f1bac4e9e0c44393cb82e6eccad) (by decide+kernel)

private theorem block3:WideCovered band 7564710 7888285:=PRB band Z1.f829 7564710 7888285 (WB 206367774775 16 0xaeb83c11a592cc53c2eced7541de37ec8469de03a7aaaa0f274562a0b8ef7f3d5550796f430e7e077709faaa83f0b817dbaabb90cfd5541f0b4abe13f5db4a82aaa0f36425e3de4ed07415550770b82eebc87634a1aaa83a2c2173c08baf2d0d5541cec54b900c5d65a8a9a60e8f905b6560ea8f455550626c722ffeff4f8a3a6983b474564e873a54d1d34c1e4490af5b55d16a929a60ee73a572d6ee817494d3074f69ab3bbd73bca5) (by decide+kernel)

private theorem block4:WideCovered band 7888286 8211861:=PRB band Z1.f1375 7888286 8211861 (WB 206367807575 16 0xb6d829c692abfcd3fa9b2b6db052f4e1562d3ff3fa5adb60a1be7ab09e9fe57cb5b6c13e11c55ea13fc6097b2c831788ee46028f8232f6590611d1dc3bc29ef0a62cb20be48338294a3db9cc596414f7af4dee977b2499b2c82982a49bedf2f5ab335d705f8311b15121ea1a6acb20a273fa7c1be7d1bcd575c18846168c16479e89baeb8308180d09b60f333375d705fa1619d7279e52a72bae0bc17cb33d043c7dce575c170f0565dcea78ac9d) (by decide+kernel)

private theorem block5:WideCovered band 8211862 8535437:=PRB band Z1.f762 8211862 8535437 (WB 1306953144344 16 0x5cba0ebe496031af047b1ab9741e7858bc138207ba3972e83bd4897712f40cfc72e5d07509b2ec55381508f5cba0e330c5ce02702031eb9741bb208b96b8602ca4172e83735b56ffaf4031c82e5d06c7f72df7318014915cba0d88365b1e2aff8b22b9741a5432b686bdfdda4972d834ca9168defbf93c96ddb06337c2d90e57ed8935ab60d23e158804efd1326b56c1b8996accbb1f8ea516ad8353f555970bbef5ca2d5b0697402aef887d9c95) (by decide+kernel)

private theorem block6:WideCovered band 8535438 8859013:=PRB band Z1.f1376 8535438 8859013 (WB 1306953144408 16 0x60c20c86a4423ecfc396c2b0610659fe21e1c0a1b7a198308331b7d1169a30d1f0cc18418fc7486ef0286408760c20c50a243856f42f8c3b061061945a1a4efa168a2183082fa5f10e1ed50aa711bf7c1802f087c25d850489dfbe0b7f33448036c25ac4efdf0582fa2266ee6119a297af83ca50d943211082f14bd7c1d9c82c835ec83c88b5ebe0eaf6a63b70241bcc5af5d075efab150b720caa3172e83a7bb988d59905b718b9741d9972c19b34828c8d) (by decide+kernel)

private theorem block7:WideCovered band 8859014 9303930:=PRB band Z1.f1377 8859014 9303930 (WB 206367841400 22 0x32c60ae60b917cb6ac6fbbd638c159f02229c8f58da87bc7182ad090441c6bb1ab2f78e3055dc0a86a6c963429f31c60bd56215701b6465dbe638c177d58aa4ce348c6c7dc7182e9c555371b89183afb8e305c7352a48e7b22f39fb1c60b746a544627645bfbf638416b190a7f21d48b307fc30833e4517767b4715c2ff8610660e22e98a4ae2a4a031c6093a70884e7254521c0638c1265e692c6e9189f481c71824741c2594823134b038e3049f132449dd42255a0b1c60929f349395d8c483c1638c123f66126b68188b883c718243ce124e9b9310d3078610494976439aee2206a130c2091f5a886f99443e5c26184124d3290a68f8877c85) (by decide+kernel)

private theorem block8:WideCovered band 9303931 9951082:=PRB band Z1.f1378 9303931 9951082 (WB 206367876248 16 0xdb58239c1906abacd12faed5b6b046a8b30e2c4dde5ce5af6d608c7cce1c08223cb4db66dac112af303924d1795fd6ddb58217dd5879cffed2abeddae904751f30e3100165305bf5d208bdeea1c59b92ca11b869a411b4a7833a0474938571d338240dc786c5f3a725cee5a6704774f00d5f2a8e4925cf4ce08e29cc1d00b9148d5ba699c11666b439dea62910d75d338221ac9074e0b0520deeda67040897f14b5e6863f45df3ca0f4cdbecfce0d84799bc67941c86285a7b22908e9579) (by decide+kernel)

private theorem block9:WideCovered band 9951083 10598234:=PRB band Z1.f1379 9951083 10598234 (WB 206367774872 16 0xeb98359f95eafcdcd0dbad75cc17dd38f8079e684656fae60b60007785b1140f6b9cf10742913512a479fdd5de3783bd1997a22734f9faf71bc1e26f6b95ab1a7a857f8de0ef809603eecb3c06c1c6f074b87304d3649d6561e37839819d7f331a4e63b16fbc1c29a4be4b19270a58f7de0e1b4462d2b273716c9bed079835b3073e29aed65df683954e5942b994d27b36fb41c3a14d36f3c666c59f7da0d72c769a71833226d1b6d074d5033f90a0987569) (by decide+kernel)

private theorem block10:WideCovered band 10598235 11245386:=PRB band Z1.f768 10598235 11245386 (WB 206367808536 16 0xf3a83ae7029dabc1572e95df507359e534f2baabe52fbea0e1f39257d29d52da677d41c690f495cffa9bd4defa838a80c8ef6d5523e9ddf506f3029181ba2a2053fbea0da6c0a28d9153f1a877cc1aa63a43aacfa74551eb9833f80c85ae5f4d4ea5d73066c689056f4698254fae60cc954204f2f52b5aa75cc19e6503ef0d4a4cd55eb9833064c7bdfe9485eadd73063a540f6ff828e455fae60c04899e8e0dd179ac75cc16eb4a3d72d5a25559) (by decide+kernel)

private theorem block11:WideCovered band 11245387 11730110:=PRB band Z1.f768 11245387 11730110 (WB 206367841304 12 0xf7b83509a274d969b2fcbef7b833f17f7061e0b2613ff7b83381506b018bb1c340f7b83302dc67c759b12541f7b8322491642c82b08742f7b83154c360f990afe943f3b830889b5dfc07af4b44f3b82fa2a35a9628aead45f3b82f35b957fb22ae0f46f3b82f49a554fbdfad7147f3b82ec44c5348d6acd348f3a82e1fec510e32ac3549) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6553535 11730110:=(_Q1 band 6553535 6917557 11730110 block0 (_Q1 band 6917558 7241133 11730110 block1 (_Q1 band 7241134 7564709 11730110 block2 (_Q1 band 7564710 7888285 11730110 block3 (_Q1 band 7888286 8211861 11730110 block4 (_Q1 band 8211862 8535437 11730110 block5 (_Q1 band 8535438 8859013 11730110 block6 (_Q1 band 8859014 9303930 11730110 block7 (_Q1 band 9303931 9951082 11730110 block8 (_Q1 band 9951083 10598234 11730110 block9 (_Q1 band 10598235 11245386 11730110 block10 block11)))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤50)
    (hT0:3163≤T) (hT1:T≤3825) (hnu:6553535≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤44229008218871759:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCV
namespace DDJ
open AI AP AN
noncomputable section
def band:Band:=⟨15,51,3101,3598,43767135969273455⟩

private theorem block0:WideCovered band 6684606 7011317:=PRB band Z1.f1380 6684606 7011317 (WB 206367808567 16 0x9a584758763d272fd5f7eb2cb08ec6f879891baab0ca59611e1bd8f0e33f52e374b2c23de661dc700ea0cab96584792103b4e89d379cf2cb08ec37c761887a5b49259611cd698ea8def48eb04b2c239c651d2aa2e8cd9d924847406239ff9bd0fbb324908ec52872e7cfa0b85a49211df978e404af3ef29492423bc941c5554e78e8f924847511238546bce7d9724908e4f607024b79bbc2249211c5758df304734fa249242b052d50fb07664f81) (by decide+kernel)

private theorem block1:WideCovered band 7011318 7338029:=PRB band Z1.f771 7011318 7338029 (WB 206367774743 16 0xa2884eada513e9a6ff82da2884e95851284c6fa86a9e784f1a550f239ef58a69e784f63610cc22ef08e39e78501edd0958f6eb91f9e784f9ccd076b2ee695c9e784ef92106456ee19989e784ea7d9050fbedc9d59e784e9bcd03c2d6d7a119a684ee779012eded2a4e9a684f0b24ff58a6cda8a9a684f5940fd1566c8ac79a684fa478fa184ec3b039a684f317cf9060ebeb409a684eac28f7e736b9b7c9a684ea87cf5fd6eb4bb9) (by decide+kernel)

private theorem block2:WideCovered band 7338030 7664741:=PRB band Z1.f771 7338030 7664741 (WB 206367774743 16 0xaaa84e4ab93c87374f465aaa84dfc3d3af8ff4a4a2aa984e5c8d3773d7454dea6984e11a135d26f4051ba6984e0f653375573b557a698505db52ae8af36594a6984f56e129d9af315d0a6984e932528cd8f2c60da6984ec25d26110f27649a6984e8e2924b7b722686a6884e600d233c971d6c2a2884f7fdd1e28a7186ffa28850830919f4df1373ba288500c851880ef0e778a2884f4029176fdf097b4a2884ecb5115356f047f1) (by decide+kernel)

private theorem block3:WideCovered band 7664742 7991453:=PRB band Z1.f771 7664742 7991453 (WB 206367774743 16 0xb2c84ef0196ed22f9f09daeb850808967adf79a0daaeb850af1d64841795116aeb85337215c738f90153aeb851fb7559ae1f8b18faeb8508bf558933f861ccaeb84f1949579a0781208aeb84e784956de777c245aeb84ec465531d4f77281aeb84e09d5525e77722beaeb84cf075523ebf6d2faaaa84fc52948be4768337aaa851b21542125f63373aaa8509e494118275e3b0aaa84f2d953e7fcf593ecaaa84ebf293d767754429) (by decide+kernel)

private theorem block4:WideCovered band 7991454 8318165:=PRB band Z1.f771 7991454 8318165 (WB 206367774743 16 0xb6d85816bd9f5a3feecd5b6d856e0c59b9fffe9d12b6d8558b0199a6bfe4d4eb6d853e50997cbd7dfd8bb6d8529d9592ec4fdadc7b6c852531d90cd6fd5e04b6c851febd8eb6cfd0e40b2c8539751871507cbe7db2c854361182cec7c6eb9b2c855f9fd7c1827c1ef6b2c854dd7978ed47bcf32b2c853a265776d8fb7f6fb2c8521b25761c17b2fabb2c850210d74f2ffadfe8b2c8504b8d70e897a9024b2c84fb90d6faef7a4061) (by decide+kernel)

private theorem block5:WideCovered band 8318166 8644877:=PRB band Z1.f771 8318166 8644877 (WB 206367774744 16 0xbae85a337dec837c1f486dd742d1a5ef3b6ea0e652aeba16b699787e0d06930d75d0ba6ec3add0982f9c3bae85d7269d20c5c154ffdd742e4f12e7985e0968f2eba16ec197319e90414f175d0b4f8538e6a181bab5bae8593e9dc44b340b578dd742be258e0b2c2046cbaeb61573316ecfdf0196d56db0ab84cb6fbea807ba7b6d855e785b44844015f1db6c2be6ecd5a801ff7082db61641e56953a0ff18b96db0b21a2b4339c7f3c99) (by decide+kernel)

private theorem block6:WideCovered band 8644878 8971589:=PRB band Z1.f1381 8644878 8971589 (WB 206367774808 16 0xc7184d34350e5bad11ca8b8e309a0a021a19ba22560b1c61315ba4352ef4422df638c25abbe87163287f5fbc7184acda90d578d0f4c6f86109d92722069861d59d30c2138a2743ff86c38358618426cfee87351986b6edc3084c9aa50e7eb30cce5386109860021beb36185d9b0c212ef624356acc2e3d16184254f188758818577dfc30849b01d0ef31b0a50377df0bd6913fa6192136162fbe175e6d7e38c642444a5f742e0786fa42688438d1) (by decide+kernel)

private theorem block7:WideCovered band 8971590 9543334:=PRB band Z1.f1382 8971590 9543334 (WB 1306953245848 22 0x1a338429de3072f97f5233d4cd19c20ff7403d311e990ff1f68ce1069bbe6925941c82fcc34670919601a858b0a23f00459b2854d245b177a82f1e4114cd9428e98659c2f1a28e810362c61130dac25b51ab46f0be316308939bf12a7f69a3646e58b1844c6e889beaf2b1a83ecc58c227d63c4c83c558cf23362c611c4f1433be3b2465137b16308dcec7197fae92314ab18b1845d8000af687471805d0c58c22d84f0568ead38bb32560c212053e63dc310145b1b0b06108f75601e0c760a2c4e798308475c610e9a4e251587b4c184237c66871608d28a741764ca10473ca1346a60c51229f1e30817c1409be64c62752418b1841b9be843f3421130998c58c20da93021d0240893509) (by decide+kernel)

private theorem block8:WideCovered band 9543335 10196758:=PRB band Z1.f1383 9543335 10196758 (WB 206367775896 16 0xe3784810b0ede0e266e5c5b7da15682832328389af78fdf68543bc0d233a5e6960236da14e8f934404c699b881db6851f0bcd09599a6463eb7da136c2c34b9136987973db585772c4e1d89565f67b36d61501ca3831ec5973a65db584e7744e0f91165a6b7b6d611e19a391b3c595fb57db58491758f1f82d2556f435d2164b4d3fc1ed294bc49d748524db4cf1eb8e50730b5d212e198415f302937d3bd348525408dbed3c64b76d34ce1617563969130923e2d) (by decide+kernel)

private theorem block9:WideCovered band 10196759 10850182:=PRB band Z1.f1384 10196759 10850182 (WB 206367774872 16 0xefa8573d55e56ae4d2c7c377d429ab3ef438ba693bfffbea1328337a9d5d348a0f1df5089994be807c9a3b0f1eb984d2d8dc8ec245188b575cc29438cd3d9ede89c78fae6137a046a19dcf43a4b9cf10a9b50ada7d66a132d5eb98435c69dda202d049a773cc251222dc8f2127fcf1f8e214e42c5d848873ea881c710a65fdae4d4939eb4b9e37854b2157e96214f0a9971bc29b7d4bee99c675d6af8de142b8c5f424e339ac49c6f09ebf2ba980909c369d) (by decide+kernel)

private theorem block10:WideCovered band 10850183 11503606:=PRB band Z1.f777 10850183 11503606 (WB 206367808536 16 0xf7b856384ca509775f0fedef70aa8c1141ebc6bba1bfcee15139aa749edd7247479dc2995a54c4e06ada961f3b8531f7c93f6c15a13b5e770a6a8e1220482b1a94fcee14a3152382cc55e56679dc28da8e458dd0ab2b45f3b850eb4089478d55177ddf509fbf950cc7b2a7b0dfbea13a95720db81d4a65877d427477240ea5ca8ad29efa84f45887ea3cb501b45df509e00c0f8d83a9db86fbea138d439ef9a153674a77d4268add3d43fda62f0d) (by decide+kernel)

private theorem block11:WideCovered band 11503607 11911345:=PRB band Z1.f777 11503607 11911345 (WB 206367808536 10 0x3ef217f3fbba0b7fdae058fde42f09f86f7019b523b5fbc85e45f4d6d37d69085df790b9c5359e3b0ecf929fef216e0f8b1eb6ad9a2907de42d2dc360fe1eb2a599f7c858f986bae8ef640c25ef90af1e8d67d776c59a2fdf215ff71aba3435863827be42b996754d4dcb0277d) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6684606 11911345:=(_Q1 band 6684606 7011317 11911345 block0 (_Q1 band 7011318 7338029 11911345 block1 (_Q1 band 7338030 7664741 11911345 block2 (_Q1 band 7664742 7991453 11911345 block3 (_Q1 band 7991454 8318165 11911345 block4 (_Q1 band 8318166 8644877 11911345 block5 (_Q1 band 8644878 8971589 11911345 block6 (_Q1 band 8971590 9543334 11911345 block7 (_Q1 band 9543335 10196758 11911345 block8 (_Q1 band 10196759 10850182 11911345 block9 (_Q1 band 10850183 11503606 11911345 block10 block11)))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤51)
    (hT0:3101≤T) (hT1:T≤3598) (hnu:6684606≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤43767135969273455:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDJ
namespace CZA
open AI AP AN
noncomputable section
def band:Band:=⟨15,53,2960,3015,41932601061619585⟩

private theorem block0:WideCovered band 6946748 7279731:=PRB band Z1.f780 6946748 7279731 (WB 206367643671 16 0xa2788c10526c58ef14739e7880b95248c8eec3289e7883527212556e71dc9e789dfc91a9e7ee20919e789c6e1194e76dcf459e789a81917ef7ed7dfa9e78980c116792ed2cae9e6894a41133096cdb639a689003d10fb6ec8a179a688a23d0e1d0ec38cc9a689e10d0a5536be7809a689ced50883c6b96359a689ba0506efbeb44e99a689a14d057baeaf39e9a689827d03e14eaa252965895a3101a5aea5107) (by decide+kernel)

private theorem block1:WideCovered band 7279732 7612715:=PRB band Z1.f1385 7279732 7612715 (WB 206367742007 16 0xaaa8812436be0bb74292baaa886c1fec638873d7e0aaa89190dec87b4f38694a6988403ba9008a733549a69883b49a8dd6372e3fda698834d928be027292b2a69882c0628a440724166a69881ebd282fe171f01ba698809aca81169719ecfa69881f38e801a3714d84a698892dc68235d70fc38a28883e2725f5fd70aaeda28883a46a5cee87059a1a2888355ea5a7d0700856a28882ee6a5813e6fb70aa2888259ba5126b6f65bf) (by decide+kernel)

private theorem block2:WideCovered band 7612716 7945699:=PRB band Z1.f1386 7612716 7945699 (WB 206367742039 16 0xb2c88ef3af443dc3c9ef1d75c4283d18ee63fe3b262bae2128c0c4306cf136995d7108627612638784a01aeb883a4a3073d23bfc5ad75c416f718325c1de9daabae206bfec1c794eeac3d5d7100c24dfb0d47704d3aeb884e64703d033b59c3d75c4b43f78b061dd988f2aaa212514b81ea9ec21e1555108400590a5075bfa5aaa883b832c659b3ab72cd554419629627f49d4743aaaa2098beb122f0e9978555510240d5796c8747a77) (by decide+kernel)

private theorem block3:WideCovered band 7945700 8278682:=PRB band Z1.f780 7945700 8278682 (WB 206367676439 16 0xb6d89780aefc9f7f294d5b6c4ad56772b4bf8053edb624d3e3b3486fb60096d911ffa5d20f67d5eb9b2c88b7cae763a3e86b6d9644230f72dc69f2f08acb222304f8fe63f8d5ad65912ea99b41a8fc198bb2c896310d9071bde41fd9644a6856c0e79eddbd2cb224c6135d473f64b5165912164da97c9fad45db2c88d9cad407f3d4188d9644485269ccbfe8c71acb2205c5b4f17bf3c0f565711b2ff9f42ef98f2f) (by decide+kernel)

private theorem block4:WideCovered band 8278683 8611666:=PRB band Z1.f1387 8278683 8611666 (WB 206367677528 16 0xbef88fde85ff0f141b3a95f7c46e062fe9c9a0c581efbe22b5c97f80650589777df10d0bcc06722827370bef880bc35fe47ac111125d744f06a44d89c2074366eba271afa1e037102ff1b75d1357f50c77bc812e42bad898bb484f340406e7b5b6c4b1b041cfa82022eaedb624ad6a0328a10074bf6db11c4a8fda6c07fe914b6d88e92a7c963c3fcbe45b6c4dbde3d788c1fd19f6db6269511e73a60fdea636db131fe0f14ed47ea3e6) (by decide+kernel)

private theorem block5:WideCovered band 8611667 8944649:=PRB band Z1.f762 8611667 8944649 (WB 206367676440 16 0xc3088e450da027e21f0270c22622eb5d225882abec30897c8ad602d21f65cf0c225bb4353102878828c30895f14d38f8a1cdb730c22532bb4990b86e591c308936a2d142aa1a51170c22469433d7168642fac2f88f698cd79d617c6bb0be2320133117e85a063bef8885a2cb162a153c5efbe2077d327cb884fdccbef889da5c8d89212b202fbe25af1f1f5a3845b35bef89b2a9c7b02a1027a6fbe245f6b0145883b89e) (by decide+kernel)

private theorem block6:WideCovered band 8944650 9402502:=PRB band Z1.f1388 8944650 9402502 (WB 206367744120 22 0x32ca229e5e53b78391ef10d96511478a295cf648f273bcb2889fcc146fbe6476af7e59444d658a0ac7f23a12931c622a8905957bb71c66b18e31146d92bbabe38de20dc71889d6915892f9c6c860e38c44add4a85236e34fddb1c624417a8546f8519dc558e3121026413ac0a8c9cdfc71885fa10f890d04625c9e38c434c107a5e1422fe9231c2253428a9ae0331751f9861127d17526da118b57b1c71886d6b0ee7fbc458332e38c434bb075c7d822ad46b1c62196343a6568114c79d8e310c23d1cf28588a1283c70885c010e5863444e09be18442afd471b4ee225bfb30c2213ab8384cc11123d41861108b191bda65888cd55) (by decide+kernel)

private theorem block7:WideCovered band 9402503 10068469:=PRB band Z1.f1389 9402503 10068469 (WB 206367745112 17 0x1b6b12b1542d99fb899a1f5db58932b6952a3204c7faf6bac489d50a19c32261731f5d623c01e4d370512f7461aeb11856b24e66e4971799d7488f99e10f1bde4b3a816ba4473fa484c40925749af5d2234d1a416b9d92a5fa9ae91170c0208f79c948d3dd748888690fc2d7c49f5536ba441ac08833e7124d203f5d22347693d568d7254af1a67122bbe2d6014a9202e2d3388e83196fae1548b025e79c4c9a9de8283e642f6d32ca2202ce24652a920363b96510f51e11e515c8fc9d2) (by decide+kernel)

private theorem block8:WideCovered band 10068470 10734437:=PRB band Z1.f1390 10068470 10734437 (WB 206367811736 16 0xefa88016000e7021668f2d97bea206a17c376ab78a328ceeb988146800f7fd19e8a18dfae620393603958ce6a1e3a0eb98805d6a0d9f5dd6850427ae6203332c38266e5a09e72df7890a1ea875b8d127fef6f9e2203e098364bd639f5944e7888098600dc4fe8e7adab77da22c0a915c3fcf09e1416e388838f9d0f27b5ca75c5ff7da22110b1120e0909ccee8db688745f43e66ed0270b1478de200cdc83cfe4b19b89badb58864a00326389026b9c8f6d62175388bf724b09a448c) (by decide+kernel)

private theorem block9:WideCovered band 10734438 11400404:=PRB band Z1.f1391 10734438 11400404 (WB 206367743096 16 0xf7c8869069d2d866adf4d4f7c8867561cf29bead523df7c8861451c8e9beacafa6f7c885ad11c71516ac0d0ff7c8851aa1c215eeab6a78f7c88462e9c3a106aac7e1f7c8833a21c211feaa254af7c8813211c44ceea982b3f7c883849dc49f55a8e01cf7c89946ddbe4bf4a83d85f3b8833d818a3fc3a79aeef3b881cf498ce723a6f857f3b8813db5b04922a655c1efa8845419877b31a5b32aeba8851a5a168308a51093eba883754a0ac518a46dfc) (by decide+kernel)

private theorem block10:WideCovered band 11400405 12066371:=PRB band Z1.f794 11400405 12066371 (WB 206367710232 16 0xffe895257556e7eb81e43ffe89422b52e7c7b77bacffe89471a4fde1bb6d915ffe893a114dac57b6367effd892ebf4c0042b593e7ffd89212149e28cb4f150fbd8914e9484b14b44eb9fbd8905dd46316db3ac22fbd88f7a1449f6fb3098bfbd89071142c7b1b266f4fbd88fe0441c7c2b1c45dfbd88f2b04065edb121c6fbc88e7453f445eb07f30f7c88da553e1da0afdc99f7c88ca873cb84aaf3a02f7c88b97d3bdcddae976b) (by decide+kernel)

private theorem block11:WideCovered band 12066372 12273815:=PRB band Z1.f794 12066372 12273815 (WB 240727448600 5 0x103e899492650f94bb489781f44cb6730cb57dd544fc0fa261b417ad3f6e8182207d12e8e2b6a0b172c6e2ffe8964bb58a6f9b8c0da) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6946748 12273815:=(_Q1 band 6946748 7279731 12273815 block0 (_Q1 band 7279732 7612715 12273815 block1 (_Q1 band 7612716 7945699 12273815 block2 (_Q1 band 7945700 8278682 12273815 block3 (_Q1 band 8278683 8611666 12273815 block4 (_Q1 band 8611667 8944649 12273815 block5 (_Q1 band 8944650 9402502 12273815 block6 (_Q1 band 9402503 10068469 12273815 block7 (_Q1 band 10068470 10734437 12273815 block8 (_Q1 band 10734438 11400404 12273815 block9 (_Q1 band 11400405 12066371 12273815 block10 block11)))))))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 15)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:15≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤53)
    (hT0:2960≤T) (hT1:T≤3015) (hnu:6946748≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤41932601061619585:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZA
namespace CZB
open AI AP AN
noncomputable section
def band:Band:=⟨16,37,4029,4058,12658818582334196⟩

private theorem block0:WideCovered band 4849611 8599864:=PRB band Z1.f1392 4849611 8599864 (WB 211735305336 21 0x1702dd7c60270de04833938b816ebcafd320ada4154ccdc0b75d8bc96c7f920867e6d05bae2ed49609c90314b5682cd6b8aa3f94bc80fabbb4166bae8116d9c240358e5a0b35ccb088bbb71ff6df2d059ae0b84378238fe97bb602cd6c2620e411c7ebc3eb015eb46b8fe9b363f164fd80af5c1f07dc7bf1f67402c057aded84055786fa1ac3602bd6cb01fbaa3b7c7dc2ac156b45bcf7caa1bdf711d60ab5bdb879a456ded7a0eb055adb853c23816f59dc9582ad6bbb1db24ab7a3f450684ea01b401d74d3cd7d302f43500820085d05e480181521a80300029660edc3120801d401a00149206de796) (by decide+kernel)

private theorem block1:WideCovered band 8599865 9188139:=PRB band Z1.f842 8599865 9188139 (WB 206366628888 16 0xc6fd71a29f469aa30ccaf1bf5be417a82958ba38cc6fd6ca61d96a7a2c4fb30bf5a53471ed378a844dc2fd65ecdbbd3b627d2bb0bf582d669633a89650fc2fd67ecd9c011a2355bf0bb5979a64ae1c8845d0c2ed634998688d61ed8c6fbb5822f5fac41872692beed5c3e96f1c261a5bcefbb5894d58b0ec860754beed60d895db7b215ded6fbb57acd55311c84e816badd5bfbd4a96aa1161daeb7562b650df0d83c8d7) (by decide+kernel)

private theorem block2:WideCovered band 9188140 9555290:=PRB band Z1.f1393 9188140 9555290 (WB 206366629944 10 0xceed7c56d335daf91cd5aceed797292b4f11913fc3ceed7641d232e8190b024caed729811ac763902085caed6e2c111d17f8f90e6caed6873907b9cd8f0147caed708e4fd581b8e71a8caed6e1c8f7efc18de209caed6b3ecf25a838d5269c6fd6d1850698328cc2ca) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 4849611 9555290:=(_Q1 band 4849611 8599864 9555290 block0 (_Q1 band 8599865 9188139 9555290 block1 block2))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤37)
    (hT0:4029≤T) (hT1:T≤4058) (hnu:4849611≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤12658818582334196:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZB
namespace CYU
open AI AP AN
noncomputable section
def band:Band:=⟨16,38,3933,4033,12576171010368727⟩

private theorem block0:WideCovered band 4980682 8473644:=PRB band Z1.f1394 4980682 8473644 (WB 206366661752 23 0x2db76942ea0d8b8c814c2cb6cdaba0a7f36df202ec16db36a70f1f4acd48029deb6cda780a7aede91fe62dedb3693d01e5e25c7f0790b2cda10b6768f531f9d9a6caf69e1a9ce14347de541b2bda5d5271bcef1f5506acaf68f031bf05e47cc2f3aebda15886e5e991f0c732baf677591aeab347ba0a4aeada417c69b9831ec3df6bab68a1a9a077dc7a7e56aaada094e664c331e7b4beaab6788e991d85c795c07aa9da266662bf251e32b82aa7684b51859a0c7839b9aa9d9fb4a5fe78f1dea24a9a767772978b85477176b069d8031800e7f8dda191017f600cc8039ef275f51d044d8035000e7665d34b381076005b0014430704994) (by decide+kernel)

private theorem block1:WideCovered band 8473645 9068191:=PRB band Z1.f845 8473645 9068191 (WB 206366661656 16 0xc2fdbd29ec3d57b14bd3f85fb6df2179936e2735e30bf6fae52d660bc49e28e17edde5f58c33e88ab2ac2fdb902eaf140f10340785db69df95529b61e2372fbb6beb9295cc7437bda5f76db06f4f904d86668dbeedb461a9c01450baacd7ddb6341932283e1510fefbb6b9e3a5aeacc2598bdd6ed4eb3495e918421f0baddabdfc8db98d07219375bb5d09115f52a0bfe8aeb76b00422154441373d5d6ed4a064358b381dd53) (by decide+kernel)

private theorem block2:WideCovered band 9068192 9662737:=PRB band Z1.f1395 9068192 9662737 (WB 206366695480 16 0xd2fdadaad463632e4dc4473bf6a77f50cfd0f92dfeacefda5fdf410974e493b0f3bf6a63d8fa16b591bd9ccefda8fc03d3bf8644b1d73bf69b6c4efe98b909b4ecefda3efd3a0a10e40289b2bf682d20e1e99b8f78ffcafd9c71236d03b63b9f632bb68de38d49f218e56b1cb0da72383b9302237162b1c368ff88e509588d3463c70da02a936aed12328cf31c3692574d352448c1215c6fda2bd733677fa2e03b71bf6842f8ca14e88aefc6) (by decide+kernel)

private theorem block3:WideCovered band 9662738 9736525:=PRB band Z1.f1396 9662738 9736525 (WB 206366695448 2 0x34bf6c969124ec5b29229ba5fb60d46903dab940238) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 4980682 9736525:=(_Q1 band 4980682 8473644 9736525 block0 (_Q1 band 8473645 9068191 9736525 block1 (_Q1 band 9068192 9662737 9736525 block2 block3)))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤38)
    (hT0:3933≤T) (hT1:T≤4033) (hnu:4980682≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤12576171010368727:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYU
namespace DBM
open AI AP AN
noncomputable section
def band:Band:=⟨16,39,3841,4008,13230930021958327⟩

private theorem block0:WideCovered band 5111753 8228499:=PRB band Z1.f1397 5111753 8228499 (WB 206366660695 20 0xb2bdf9f54cb381bfb1d27657bee1e9904497f3ef92baf7cd74b12639fe349ad75ef760b60f8c1fbd685aeadf75acbda0aff687ad5d5bea34576076feac49ebab7c9e32e2611fd0f3c5556f787c5ae8f5f98bc9aaadf4e06b1ce2ff1f235553be62615f189fe199aeaa77c494ab7670fbe9de534ef73cf558953f7410ca69df04e6a7be5bed5cbb4d3bdfaed7467e5d86eba9a37d3332dfbfbbac47fd346f949e5ad80d74f64fa28df0008b3e0b2e8c741451bdf58961ad0dcf43c417b7015a007217799f2102fee01aa00815272ab92) (by decide+kernel)

private theorem block1:WideCovered band 8228500 8829317:=PRB band Z1.f849 8228500 8829317 (WB 206366694424 16 0xbeede008945653686b985beede6d234333ee8626d6beede4f3f41ff41859427beede2fbd413f9e850177baede013b3fd1c5846ec8badddc0cb3e167783dc19badde2eaa3cb20583496abadde155f3bdfa782b6bbbadddf42c3ac95b82240cb6dddc8a43986a581915db6ddd8fc3389f5b80feaeb6cddfa58373ea9806bfeb6cdde18d365fa67fd94fb6cddc5cd35cb407f46a0b2cdd9c8434b05d7eb3f1b2bdddc403346877e2142) (by decide+kernel)

private theorem block2:WideCovered band 8829318 9430136:=PRB band Z1.f849 8829318 9430136 (WB 206366694424 16 0xcb1df72d568f33b8fe478cb1dfc33364d5548f51c9cb0df95dd621dae8ebf1acb0df6cdf604ffa8e2c6ac70df337a5d61b48d99bbc70deee9a5a29498d070cc70deefeb5764278c745dc70df1b9e55627d8be1aec70def3215360ca8b4effc70dec39b5139a58abc50c2fde91274fcc9d8a29a1c2fde44d04d1b8b8996f1c2fdeb7ac4af609890442c2fde9af44a0973887193c2fde7236486d3d87dee4befde3edc469df5874c34) (by decide+kernel)

private theorem block3:WideCovered band 9430137 9917760:=PRB band Z1.f1398 9430137 9917760 (WB 206366728248 13 0x6b86f62b092ff661975540d70dea238a509f9f2d895bae1bcf6bc482f41658c7fb4c37915888a5e12cacfa7e986f072fd0c4523950ca0d30de99fea3522b528f3e39e1bcd6e4435b25a4f9d0b3c779091e81fbf749aa49e78ef2c250f69c0e92c1e3cf1de3b769dd1dc1245e699e3bc463d3a417f24672173c77808da70627f4884eb658eeeeb6cd81904907727) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5111753 9917760:=(_Q1 band 5111753 8228499 9917760 block0 (_Q1 band 8228500 8829317 9917760 block1 (_Q1 band 8829318 9430136 9917760 block2 block3)))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤39)
    (hT0:3841≤T) (hT1:T≤4008) (hnu:5111753≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤13230930021958327:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBM
namespace CYO
open AI AP AN
noncomputable section
def band:Band:=⟨16,40,3754,3982,17488788244871693⟩

private theorem block0:WideCovered band 5242824 7974730:=PRB band Z1.f1399 5242824 7974730 (WB 206366693495 22 0x2aab87bd2d54fa35f35e95555c3e62ca75b9ef91b13aa9e216865259d97c436e554f100a428ad07bdfca96aa787a571427a5deebcdb4d3c392849eaf16f6ca36a69e203624df85d7b1affd3470f918a68c94bd687229a387759d308165ea1b21451c38878960282f47959a28e1f04d49f75579f291513f0f15524a3a5bcd43ae89f880ca943d734e5796944fc3da8ea020c272287d9e7e1d3764f554d38ca234f3f0f043a719ea9c4003e79b87d999354384e0d7ae0c9c0048a00feb1efd7a0063e00244007f36b7a1b4831f000c880273f3b86bec107800670013920d7943c083c0032e009b786286ac) (by decide+kernel)

private theorem block1:WideCovered band 7974731 8581820:=PRB band Z1.f852 7974731 8581820 (WB 206366693400 16 0xbade2b0236df5d905e57975bc51d8cda28ba097a16eb7897841ad52d40e5275b6f10d4834a1c0813617b6ce26e616691330143c16d9c4e6eac9f3420036a6db3893d498e10e3fbcb95b6711215b14f6b7ee53bb2ce1e13260b542fca207657c4b5a2bce6d1f6f332caf88fcbd750233e944ad95f10e1eadf4557c945eaebe1ed6f5a52caf8004f5d7c47f74b0a061edafc2bab88b1455e9f53d6bdcd757108cc2b44357a4382) (by decide+kernel)

private theorem block2:WideCovered band 8581821 9188910:=PRB band Z1.f852 8581821 9188910 (WB 206366694424 16 0xc70e3e9574c7c158c362ec70e3bdb04b0ada8ba1f7c70e38ae74986cb8b0dc0c70e34d4047e28c8a7989c2fe3079246e2ce89e552c2fe2ea8544caa689511bc2fe3537543220688bce4c2fe326d141f87e8828adc2fe2ef6840b434879475befe2a6593f416587003ebeee27d643e1281866c07beee2fcba3caf9385d7d0beee2d43d3bc0dc854399beee2a0ee3aba7284af62baee25b89398a37841b2bbade2836c380a068386f4) (by decide+kernel)

private theorem block3:WideCovered band 9188911 9796000:=PRB band Z1.f853 9188911 9796000 (WB 206366727224 16 0xd71e28ec8b968e2655e6834cb8c8ab2f1f70494e569d32e2f5faba60aaa5144cb3cb8b1602e0d6ce93bcfbcf2e28f2e35ee12a4ca3133cb8ae0b2cf022c92948dcf2e2996fb25e5f248015b3c789fa64c5d2be916c1fcf1e259bcb00599a435f9f2c788bca8b9fd209043b0cb1e1fba12cd05723ebde72c788ef8aadecfa8f1b42cb1e22192aa7ef6a3a1c2f2c7880e5ea5dc868df2d4c70e1e583a8d01c2357a771c386e5e69e7fc88cca66) (by decide+kernel)

private theorem block4:WideCovered band 9796001 10098995:=PRB band Z1.f1400 9796001 10098995 (WB 206366728216 8 0xdb1e3a3262406e166864cf6c78dcc4c8c64cd998722db1e33db8a22c99a63cbaf5c78bffac84eefd985eb4d71e2a8149fadf8a5f29f75c78c59107aecf2973646d71e2f2319e2c78e5a883f5c78b0226751e01960dd8) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5242824 10098995:=(_Q1 band 5242824 7974730 10098995 block0 (_Q1 band 7974731 8581820 10098995 block1 (_Q1 band 8581821 9188910 10098995 block2 (_Q1 band 9188911 9796000 10098995 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤40)
    (hT0:3754≤T) (hT1:T≤3982) (hnu:5242824≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤17488788244871693:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYO

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option autoImplicit false
namespace CYI
open AI AP AN
noncomputable section
def band:Band:=⟨16,41,3670,3956,17619782869255014⟩

private theorem block0:WideCovered band 5373895 7789007:=PRB band Z1.f2110 5373895 7789007 (WB 206366693495 21 0x14d3cc283491767676d9cfa69e6495e47703f3b22085347322a52349109d6b9469a398bcc91807bcea3125451cc21c88a2bc67482d3a28e6353f43f97d39f68a514731abba1b0199cd5d5689f9886ad0a97f4e5832b3cfcc12d683a5b6722bd69e7e6158f41212938cb0bcf3f3120c2026629c4016279b984e10fe8c6ce0d5333cdcc9f5892c05defd4da9e6e6373348e2e0f79f8dcd3730c532408d77baa57269b98bdd51d875bdc273934bcc89b68cf47ded7ddd05fe402dd007d4eb6740f030f200fd80269a3aef28011390080c0133e0d2cb46083c8040200996464b7aa) (by decide+kernel)

private theorem block1:WideCovered band 7789008 8402369:=PRB band Z1.f856 7789008 8402369 (WB 206366693400 16 0xb6ce6d2a85ab3eb006b836d9cd571ab32055fe800adb399f3c563865bf8521d96731b012bb7f47e7484b2ce67a4a558a2afbbd8b657cd366ca8fcc1f5241acaf99d3094dcacbe59a3d95f320ca291ded7c1d87aebe64bfe50b874f70f915d7cd0a589f1d3debc826bab999c113a8a2bd2e25575732033a6caab79c68baaae613bc4cd124f26199555ccc92e968b45e26c36aa7995aa1297833c02a7554f31d8c24e2e7776f8e) (by decide+kernel)

private theorem block2:WideCovered band 8402370 9015731:=PRB band Z1.f856 8402370 9015731 (WB 206366693400 16 0xc30e709c577fe6313236785fce84daec1fe223efd30bf9e390dcd96144331ae17f3ab4a38c5f987d076c2fe70e456f79670e756f7dfcd622cdc818e1a93e2fbb9c2f99ad2d443079cdf7739aa3349762857979beee705fd685e4709c7757ddcd7fa0cd58be1137eeebb99948d92783c1dc1e5d7734e0931a4fc83227dbade6edf7611b0305197d75bcd752cbf7eb207dbfeeb799d20978ac640b0a05b6f31d13ae97da80cb80) (by decide+kernel)

private theorem block3:WideCovered band 9015732 9629093:=PRB band Z1.f856 9015732 9629093 (WB 206366727192 16 0xcf2e688502afe294976d2e7973616e14c95e6495f9b3cb9a924aa28d9923844f9e5cd058b4f5677912c68cf1e661c6270518484b54e58f319a2d2f71ce4003ab2c798fc6a92c1451ed657963cca9e0482ab48ed56bcb1e6387a236097c71fd6658f30b75515024636a7b71c797bd4a87b0af1a285d8e1cb7983427f708c7e6fc70e61196a03a45c5f45863872fc40cfd6b2a2d4bc71c397793a7d64cd157a658e1cb70ab3d73708a2772) (by decide+kernel)

private theorem block4:WideCovered band 9629094 10242455:=PRB band Z1.f856 9629094 10242455 (WB 206366760984 16 0xdb3e6a10453024eb38932fb67ccf7e8a45b2fe6ecf636cb995bfd457a8fcd8f0ceb9731c3f88639a59a885ad73e611ad4ffba1d33e537ae7cbd7f69e593166573735cf9805283ae83e4c638eeb9f2f44a471da7998315dd73e5cecfcdbc4152f373da67cb66b81a75cf65c177f4cf96694033712f4b3810699f2d0dac6277be95da61d33e598bc8bf63a92a8945a65cb12151776f6a52bb8f4cb95d09e2d930aca0c9267972ae554584d20938364) (by decide+kernel)

private theorem block5:WideCovered band 10242456 10280230:=PRB band Z1.f2111 10242456 10280230 (WB 206366760984 1 0x6f97333366956a0c9cdd26) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5373895 10280230:=(_Q1 band 5373895 7789007 10280230 block0 (_Q1 band 7789008 8402369 10280230 block1 (_Q1 band 8402370 9015731 10280230 block2 (_Q1 band 9015732 9629093 10280230 block3 (_Q1 band 9629094 10242455 10280230 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤41)
    (hT0:3670≤T) (hT1:T≤3956) (hnu:5373895≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤17619782869255014:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYI
namespace CZT
open AI AP AN
noncomputable section
def band:Band:=⟨16,42,3589,3930,17946072568172132⟩

private theorem block0:WideCovered band 5504966 7634957:=PRB band Z1.f2112 5504966 7634957 (WB 206366693463 20 0xa68ea5de0419e61f4800da28ea5f1f40c203f3e8c6a28ea87453fbe77f3517fa27ea70913f23e1f2ba38a27ea54953e75c9f222f19e7ea5f133da9fff18baa9e7ea73f33ce44bf0f4639e6ea62133c7453f05d1b9e6ea4b083bd641efc5d49a6ea4faa3b203bef2e8d9a6ea62273a644dee97469a5ea51c739defdedffff965ea3e5e394b0bed68b8965ea41e538ce25ecd171965ea51593824cbec3a2a964ea433537a9b3eba2e2924ea32af372217eb0b9b054e8058400da136a745405ce80369007b32e945c6045e80264004bb266e8a9) (by decide+kernel)

private theorem block1:WideCovered band 7634958 8254590:=PRB band Z1.f859 7634958 8254590 (WB 206366693399 16 0xb2cea63e6513f77f7d1facb3aaff0d3e1c4fd5d37b2beacc944e4b63f317c2cafaa5ae5367807c2ea9b2bea49834ce27dee5d8abafa9fe2d2e5d27b001baebeabec44a2063e9a352babaa501d25578f9d18caeaea5a764868fde4e916aabaa29e51cf5ff8a2feaaaeaadea465e43e02edeaa7aa30bd16a66777470aa9ea602344da2bdb74a69a7a9c1dd0f75cf645e2a69ea998542c3b7d6ba6e9a3a9f82908661751754) (by decide+kernel)

private theorem block2:WideCovered band 8254591 8874224:=PRB band Z1.f859 8254591 8874224 (WB 206366693400 16 0xc2feb85f368266b0ed1e185fd64936cddaee1b46a6fbfaaa0b994e26431d315f7f590e831711385a31bbeeeb6ee560c2350a17a97ddd64e28bf252611d236fbbab02e578e06c1eea35f77531702ede998345febaeeacd4e5baeb7055d6f75bd63facb35692085dc2eb7ab5bf56280940c014dd6f535b7abb34580e8e2b6deaa9e855c81100a3376dbd5905ea9b445fee952db3ab648d4db9ebf9186db67546dfa939d07e8bc5) (by decide+kernel)

private theorem block3:WideCovered band 8874225 9493858:=PRB band Z1.f859 8874225 9493858 (WB 206366727192 16 0xcf2eaa4f7a337a0c86eb1679753c9b913bd8241186f2c7a90980868fb31f5da9963d4dc9041599a8f178dcb1ea7ab0203cc8c74023658f52d240fdba5237a3ff2c7a8ca867ca6ad1aa3718e3d3fea53d1af98cba70c70e9ea7b1dd61bc61194e38751b1e0e8568e2e2f8b1c3a871707358eb15e9378e1d3ee5638d5da8a5d54c70e9c5779bf4cbc4e306e1874c7fd8db4d0224bb1b0bfa7824a6ac2a7112eff85fd3c8c7347775880037) (by decide+kernel)

private theorem block4:WideCovered band 9493859 10113492:=PRB band Z1.f859 9493859 10113492 (WB 206366759960 16 0xd74ea2cc91b5ea7e6947535d3a83f4e6a77e599ba8dd74e9e98319879f6648d1b5d3a81631629d43988bffd73e9eeb997fa1825fd2e35cfa7594a5d2a66975d71d33e9bb96d695d765b18ab4cfa68870585b6f962ee2d33e9a61e554d142565e6f4cfa6a63553039a950054d33e9964a544799a51a4374cfa602ae4f27a893d1c6cf2e9678e134485a4ce9ff3cba5341b4bacd392a338cf2e974cd524d166482fc73cba5934b47d8379174a9) (by decide+kernel)

private theorem block5:WideCovered band 10113493 10461465:=PRB band Z1.f2113 10113493 10461465 (WB 206366761016 9 0xe33eabb61519b3799fa119e33ea95bc912aae79f0c0cdf3ea6bd1d0bc6bb9e74c5df3ea31fc900cde19ddd7edb3eab12690d1db09d4637db4ea7f790ffb0049caef0db4ea8bf7cf3f7849c17a9db4ea6d31ceb93ec9b8062db4ea4dab0e346ca9ae91b) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5504966 10461465:=(_Q1 band 5504966 7634957 10461465 block0 (_Q1 band 7634958 8254590 10461465 block1 (_Q1 band 8254591 8874224 10461465 block2 (_Q1 band 8874225 9493858 10461465 block3 (_Q1 band 9493859 10113492 10461465 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤42)
    (hT0:3589≤T) (hT1:T≤3930) (hnu:5504966≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤17946072568172132:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZT
namespace CZM
open AI AP AN
noncomputable section
def band:Band:=⟨16,43,3474,3903,30411606095906251⟩

private theorem block0:WideCovered band 5636037 7474634:=PRB band Z1.f2114 5636037 7474634 (WB 206366692439 22 0x289fbaee95cb9abb906e5513f755fa3909557174fb9e7eec155709142e1b8593cfdd9b56de2395c10d7679bbacc09b968cb7d5474d3775598b697e76f11bf9a6eebf486bc8aadcf1e134ddd7c4ad597e5b78082697ba9995a799cb6a3a8cb2f7531a34668f6cae82965eeb88f677fd6d82b672cbdd5b9acd913dadf392593ba6431977c4b5720ac92774f42326b616a4b46924eea86b63ec82d364ef249dd3ae8c6238da4669e48fba2f9d88d45b4406c471f74876b0baaf67e8098e3ee9b66606a9ece9e740c7d80dbc03555b9ad9ac107b01b7406a7d322997820f6036380d3d65f8cb6) (by decide+kernel)

private theorem block1:WideCovered band 7474635 8100539:=PRB band Z1.f862 7474635 8100539 (WB 206366693399 16 0xb2beea7f4461fc7ee6aeecafba6f05153787b01ecb2bee7332450cebe9a476bafbb8ac90ccff79d04eaeaeebcea424c41e4ddfebabba59f107e18f89eb0aaaeeaf18410335e01786aabbbe26cfe3e3f76d12aa9eec67e3f39d7db510eaa7bab454fa137f63b74a69eec91c3d994fd68a969a7bb8af0f35657509d6a68eec3863c2bb3d1c41e9a3bada64edf7873d838a28eebb7c3afb35ccfda68a3bb78d0e801872a699) (by decide+kernel)

private theorem block2:WideCovered band 8100540 8726445:=PRB band Z1.f2115 8100540 8726445 (WB 1305878321272 16 0x617f72105ace7ec10a4f5abefee75345802c82123b797ddde7a7eaa7b4e41fb07afbbba444d5320b8835d405f7772daba9fad210588e2beeed503d5436b8e08ae8b75ddafd54a6e0dd40c969aeb7bb5f053d956080fa035d6f71be527c56e100c268badee06cd4ef4c01ff219575bdba79a9c7cc03f97cb2db7bbe3a52b3b897e96c75b6773c43a53fcf0fbfbf0b6cee67bd49b83c1f594a56d9dc9be09228b83e662d6cb3b78d752439207c338a) (by decide+kernel)

private theorem block3:WideCovered band 8726446 9352350:=PRB band Z1.f862 8726446 9352350 (WB 206366726168 16 0xcb1ee52e4386be38eb49ecb1eea3c7b6c9148e1bcfcb1ee7fac3664988d8300cb1ee4c2a35a4d38cea31cb1ee04beb4c8128c5162c71edfb3ab3bf398bb893c71edf3113350668b1fc4c70ee3de531d69f8a86f5c70ee0a2cb1372b89ee26c70edc4f7310d29895557c70ed8c39b05b9d88bc88c30edaadeaf69068823b9c30ed645d2f86cb878aeac2fedd31fadc88b86f21bc2fed83e52d476586594cc2fed33a92d5ff885c07c) (by decide+kernel)

private theorem block4:WideCovered band 9352351 9978256:=PRB band Z1.f862 9352351 9978256 (WB 206366759960 16 0xd74ee0c2f538ecd26106435d3b7d7b14c767897a8c1d74eddd6312a940a5c3fcb5cfb716954964dc967723d33eda52111d970a5779534cfb6e230452d30954585d33edbaf65103b7652b2db4cfb698f042c0489413e6d33ed8e2650584ca4dec5f4cfb5d2654083fa92e248cf2ed589c8fbb8364925e73cbb60f103d0bc291b0aacf2ed79740f1930e445f6f3cbb58f203b6505907f0ccf2ed48c78e9491a3f98f73cbb4a13d39bfb48f4d6d) (by decide+kernel)

private theorem block5:WideCovered band 9978257 10604161:=PRB band Z1.f862 9978257 10604161 (WB 206366760984 16 0xe35efad6e11033ab439d03c69deed5ba07c09684d6cb7d7bcff3e3df508504e71efaf7888c0775775a00414df5ef15c0ce2b1693ed68bbebdde3769b5fc127b49db7d7bb4e1f3551facf1cd3efaf756dac66dd479da0d8db5ee85f94c61b673a1013b6bdcbdfc17ee3aa71bceb6d7b9e2912e2f87cdeb35edaf72ef9859db1f9b3d9cdb4ee41c2caea3d535499bb69dc5095155ef5e682ffb5d3b81b4a296946ccb997eba76fdeb84ffd5d98da5f) (by decide+kernel)

private theorem block6:WideCovered band 10604162 10642700:=PRB band Z1.f862 10604162 10642700 (WB 206366760984 1 0x71af7ed7848d1000a2650c) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5636037 10642700:=(_Q1 band 5636037 7474634 10642700 block0 (_Q1 band 7474635 8100539 10642700 block1 (_Q1 band 8100540 8726445 10642700 block2 (_Q1 band 8726446 9352350 10642700 block3 (_Q1 band 9352351 9978256 10642700 block4 (_Q1 band 9978257 10604161 10642700 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤43)
    (hT0:3474≤T) (hT1:T≤3903) (hnu:5636037≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤30411606095906251:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZM
namespace CYJ
open AI AP AN
noncomputable section
def band:Band:=⟨16,44,3402,3815,30005041600743961⟩

private theorem block0:WideCovered band 5767108 7268529:=PRB band Z1.f2116 5767108 7268529 (WB 206366692439 20 0x9e6f26a27681f7eddd16334de4d6f2cec31db9396a69bca0dc197db7b6da01cd37938d63287776d19ac9a5f2678064223ed8feab2cbe4e88cc612f5af93fa597c9ee2188a1fb5a5534b2793391b0b0b76ab04f924f2629f608022d42bf1249e4dd78bef01da5ee86493c9b24d7a4f3b470a5491f92e06af01916846f38e3f25c395d2d32cf59391c7e4cf06b86a859c491638fc97cf96de1fb33bf74717928af2d5ff365dd978a2f254bf5a205eca8681145e4bc8eb2762592a3a414fc01a600695172074902c78016e0048d061a535) (by decide+kernel)

private theorem block1:WideCovered band 7268530 7900706:=PRB band Z1.f1402 7268530 7900706 (WB 1305878320151 16 0x575f91403bee035e238895d7e3fbb6fabfaf7f3cb575f8da8abeb01fdd65d3555e2ea6ef97d976bf1d555792215bbbf0fd89319553e4838aecbc2758a6f534f92a233a620fd3c05d4d3e4a140e78fdf455c0534792a7bb8f741ceeda54d1e4b454e18abf32112514793950379713ca1aed451e5059adb0dd71ec64513f92ee5367acdc5483544fe4cd30d7a1d70b7b64f3f93fe1b526c7c0757d3cfe4f650d22ea6f8308) (by decide+kernel)

private theorem block2:WideCovered band 7900707 8532883:=PRB band Z1.f2117 7900707 8532883 (WB 206366693464 29 0x16dbe71a668c9908823393b6df396b545d64e40f3345b6f9c46822b75d20664f2db7cded3d147a190298236dbe6d9728997fc80fee5b6df35b614458c84058dd5b679a4fa21ff3e201923acb3cd14ed0dfc31002ec7659e69b8a86325c7fca37b2cf3589442acea3fbe8659679b3dda10e531fcbf82cb3cd70d1075a20fdc569659e69d3682ed207e9588b2cf34130412b3c3f242ed9679994fa06ece1f7ecc6bafcc852501c220fb5c0d5d7e63df88034307d60daaebf32b923f9f983e89d7d75f99ac71f9de51f31a0ebafccfa44fb5e90f8f2b15d7e665be7d064c7c2c2caebf3276e3e40be3def80d75f98cf71ef2d81ee4756bafcc31c4f675b0f68955659e422308869767af77eb2cf1c1f543c84cbd2e93d9678b06aa1dafc5e70b42aabcc0b8ced0e60f250f3555e5eec27605fc78db4e) (by decide+kernel)

private theorem block3:WideCovered band 8532884 9165061:=PRB band Z1.f2118 8532884 9165061 (WB 206366693496 22 0xcb1f316b4621bba22f64172c7c9f00184ea708b3eaecb1f2436960616422a915f2c7c041758b949d8a0a00c70f3305258f73ea25bea71c3ca04116b66a488d552c70f1958a5b37b2e20ebeb1c3c3ed2d635b7a87a0a3beff3f5764e2bc821c1932fbfcf8d1536844086b921beff3d18a4d35ba219afd6fbbcef17d3280c0861ecac2ff1fca457cfae617467b0bfc5cf995f4279853747baef3c9ca49e45821273c2ebbceefed263138844fc5baef3ad2f4932ac2100a66ebbce6e3122d5a083b56dbadf38a214854c020da106db7cdd5311f30a8831b16b6df36f0f4760ee20b37aadb7cde3811bbf808280bf) (by decide+kernel)

private theorem block4:WideCovered band 9165062 9797238:=PRB band Z1.f1402 9165062 9797238 (WB 206366726168 16 0xd33f2be78bfd7d3957e76d33f2ca21be365c94e41fd33f2f4713cafa09449c8d33f2d3a4bc2b6993af71d33f2a5e83b369d93151ad33f26bd9ba31f9927ac3cf3f22e1f390f0291e06bcf2f26739b7af74914614cf2f2806f36eed790abbdcf2f25d1636316e901166cf2f223ef357db98f770fcf2f1d25e34bc408edcb8cb2f1c6a2b3db4f8e4261cb2f1c22c334f8a8da80acb1f1dc8e3279df8d0db3cb1f1e364b1814f8c735c) (by decide+kernel)

private theorem block5:WideCovered band 9797239 10429415:=PRB band Z1.f1402 9797239 10429415 (WB 206366759960 16 0xdf6f272d3d7c4eea7c8f9f7dbc9a0a25c3c949e8990df5f24cf4d66974677bce77d7c8c0be5709ea9d54e2db5f2160c9549f5272ea2f6d7c7cec9526b189c2034db5f20ff3d3e2e626e17736d7c7eb844dc34f9aeb85db5f1e41912fd35e6944bb6d3c73b2e4aba4c99b6d7d74f1b22b5234b7a6472035d3c66f3d46c6ab988229d74f1bc3c512ecfa5f9f4b5d3c6a51d437170974d7bd74f196fe50a8de25acc935d3c5f7c5414acd9618cd) (by decide+kernel)

private theorem block6:WideCovered band 10429416 10823935:=PRB band Z1.f2119 10429416 10823935 (WB 206366761016 10 0xeb5f34a3f90f193ba528ffe75f39a8b910f3faa490f6e35f3623b503fd98a3f69fe36f32f234f8eedea35c48e36f2fbdfcedb274a2c1f1e36f307f0ce3f20ea2279ae36f2e309cdbeb82a18d43e36f2bd900d40440a0f2ecdf6f296e80cc25a0a05895df6f274ce4c640409fbe3e) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5767108 10823935:=(_Q1 band 5767108 7268529 10823935 block0 (_Q1 band 7268530 7900706 10823935 block1 (_Q1 band 7900707 8532883 10823935 block2 (_Q1 band 8532884 9165061 10823935 block3 (_Q1 band 9165062 9797238 10823935 block4 (_Q1 band 9797239 10429415 10823935 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤44)
    (hT0:3402≤T) (hT1:T≤3815) (hnu:5767108≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤30005041600743961:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYJ
namespace DAW
open AI AP AN
noncomputable section
def band:Band:=⟨16,45,3332,3560,42650136169644217⟩

private theorem block0:WideCovered band 5898179 7135173:=PRB band Z1.f2120 5898179 7135173 (WB 206366659671 21 0x269bda05faf545f6cdfc59a5f6628abbb285b10f9a697d8f2eae9f8d6ba807965f669d2b83e25ac30a2597d9ec0ad8ed76a7049964f65f5ab5237da751aa493d970f2cd60369388b924f67896b1c17da272b2493d9c672c0df16800cd923f6589caeb6159d93ba38fd98d22b59f766c90f8e3f67882aba79d98b4c238bd99a22a966f6591518a2f65456a939dd93d5ca28bd9beda9e31d6459938a2f66c6aa681158ef6ce287d97202950476321d4861f65ac8a3d9658a17d6187d9b03a8a64f61ea1604bf4073c033f038538dc107d01cc80cf2e5edebb) (by decide+kernel)

private theorem block1:WideCovered band 7135174 7773622:=PRB band Z1.f2121 7135174 7773622 (WB 206366659671 20 0xa69f70630d30459da76da9a7dbed7b48dd6764fc7a69f6ef10d139e1d8075e9a7db89934194a75b3e8a68f6d476cf8649d597e28a3db1013393fc751809aaaf52262e067e5d32866aa7d497c3783e9742e3aa28f6dd92c98dc1ce496e8a3db471b2240073446ca69f5e59acfad53cbd9f29a7d6591b492aa725a9da68f541fad25569c6fafa8a3d7a7b335af27122dfa28f6189ecacfb9c21c0289fd7cf4b230026feb219e7f6464ac590e9bd3d0a79fd992c30e3526eb3639e6f62b00c1c0f1b85e1269bd8f53affd726d7ba4) (by decide+kernel)

private theorem block2:WideCovered band 7773623 8412071:=PRB band Z1.f1410 7773623 8412071 (WB 206366659608 32 0xb6df75e92fa25e402dd3db6fba48e7c49160036e2cb3dccaf3dd67cff7f91659ee32e9ec2177f71d9b2cf72502f4af5bf91f4d967ba8f6794c65fb57eacb3dd985bc4b76fd1015659eeb059e08317e3a1bb2cf747b0eef133ef615d967b9b7676f789f678f2cb3dc9163b3888faa0995d7ee1c41d6b357d025daebf6fbbcea2563e5a36d75fb88c7746cb5f199fabafdced3b9bacaf8311d5d7ee7dd5cba8d7bca9faebf731e2e4f6c3dbe57d75fb914b71e2a9ecbb02bafdc4b338b2caf5c1a15d5ee02c5c39787a92e1aaaf6edeae0be73d2278d557b789b6f9b69e7dc0aaabdc1c6377e32f35225555ee4501b93b4795b23aaaf71b40db7c43c8699d557b877d6d5479e2fd12aabdc065367346f0e2a9555ede389b1345782365a69f6e160d7a3abbeabad34fb690a6b4fa1de1e169a7dbb14b54aaaee732b4d3ee05c5a7ea076eba6) (by decide+kernel)

private theorem block3:WideCovered band 8412072 9050520:=PRB band Z1.f1410 8412072 9050520 (WB 206366693400 32 0xc30f625564bbbe7143331861ec417a96701a272ea70c3d85f0d2b6c8c4bedce187b0709a53e48892fcac30f6028149f5b111c3b585febedd2931ec2224faefbfd7a8552492cc422fddf7faede3245acb87f80cbeff5d8fa4810130f54397dfebd8e08f1d3a1d70b6fbfd80cd51c11c43871edf7fafd1c234bc386c04ebeff5f16546458f0ce4bd7dfebcf908be3421891befbfd7712d15e0f42eb3fdf77ae849a28e0e858890baef5c37b44bbef0a754175deb6b1c88593e13b2c6ebbd715210ef33424f60dd77aec7121a19a8450d2baef5e00542cdef0805c575debaf5084f91a0ed3ceebbd73b4908c9341b381dd77ae28f20f2ce831914badf5b97f4175690596496dbeb5adc823fca09f4d6db7d67f31031664117a2db6fad574201ed481e156b6df5bbb43fd19f0326cd6dbeb91427ed6aa0515dadb7d701d8fc49b407bc35b6fadc241f679880a997) (by decide+kernel)

private theorem block4:WideCovered band 9050521 9688969:=PRB band Z1.f2122 9050521 9688969 (WB 206366693496 16 0xd33f607366a94bb24f5e274cfda773d9f157c933baad33f6692e666b6b24a7f2f4cfd89ebd980da49203ecd33f5be9864a297245a0374cfd43f65934d1c90cc2ed33f49b3663896f240c13f3cfd48a5984b96c8f9470cf2f5d53a5d39fd63be2473cbd5a0c97afb148e5cb2cf2f480d25e8977237034f3cbd3bdeb7312738d24f4cb1f5f81e5b15a623224572c7d68069694a528bed36cb1f4f94b55db3862d455f2c7d130ab6bcd488ab577) (by decide+kernel)

private theorem block5:WideCovered band 9688970 10327418:=PRB band Z1.f1410 9688970 10327418 (WB 206366727192 16 0xdf6f60dab24395d4ecabd6fb7afa5011aea6a73e66f6d7d7629a89e38b38bb79b6beb78fb43aa5b9bc1dddb5f5becaa0d263cd92ff6dafae680500cdda6a287f6d7d6e9a27eac1733dc81b6beb44213e0e32995261db5f5889b9e9d45cc5b416ba7ab2664ef275a606a8f5d3d610967443012efd89ae9eb163b3967fa96e2e5d74f5750b9c3e17cb23836ba7aae4b4dfb38656ac9f5d3d4e89e6dfd1f2a1e91a69ea130c35db80947368) (by decide+kernel)

private theorem block6:WideCovered band 10327419 10965867:=PRB band Z1.f1410 10327419 10965867 (WB 206366727192 16 0xeb6f798c53cdd9853a9b5f3bfbb0539d043f69ade339dfdca06adcff694c375bcefee69c76a8555a57fcee77f70f52336b38d271f7f3bfb74b398cdf569120438dfdb22b6c0e347475863c6fed40a05cd8baa31052e37f67bcd2d0817d13a39f1bfb48e1d5b87a28762538dfd9d804a8ef1342796bc6decbb0d52a9fea0a0d6df6f63e9a281bd4d0027befb7b0e78536c7ea7da4637dbd7fde6978b273d9a73bedec423549a7a39e3159) (by decide+kernel)

private theorem block7:WideCovered band 10965868 11005170:=PRB band Z1.f1410 10965868 11005170 (WB 206366727192 1 0x1d6fef8db47e3484a7ecf2) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 5898179 11005170:=(_Q1 band 5898179 7135173 11005170 block0 (_Q1 band 7135174 7773622 11005170 block1 (_Q1 band 7773623 8412071 11005170 block2 (_Q1 band 8412072 9050520 11005170 block3 (_Q1 band 9050521 9688969 11005170 block4 (_Q1 band 9688970 10327418 11005170 block5 (_Q1 band 10327419 10965867 11005170 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤45)
    (hT0:3332≤T) (hT1:T≤3560) (hnu:5898179≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤42650136169644217:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAW
namespace DAF
open AI AP AN
noncomputable section
def band:Band:=⟨16,46,3264,3300,45454847903335488⟩

private theorem block0:WideCovered band 6029250 6996331:=PRB band Z1.f2123 6029250 6996331 (WB 206366630007 18 0x2697e235f0b2136cd582d72cbf0c85057eb326a2404965f8b5782b6d6334c34ecb27c53fc1587a39a3a4da493e25570ab105cd0979f249f179c8547bb267ae68923f8b44029ec65338880c71fc548414c620999ce6a38fe27960a4e05ccbac651c7f1741851be866538cb8e2f8b294288da1324db24517c54c21423cd98ff7f628bea40d23b64d1c6c12d145f38930d331f8e2c32f8e3fbede5915240f112e44517cdd6231940c583abea28be4890161bf59bf60580a5f002c000e6e05e755e) (by decide+kernel)

private theorem block1:WideCovered band 6996332 7641052:=PRB band Z1.f2124 6996332 7641052 (WB 206366594167 20 0xa28f99f43105463a4bee5147cc925866561d124a68a3e60d6c23dd8e7f4eb451f386860729473abc2a28f9bcc3011be39ae875147cda957ed681cc396e8a3e6b56bebcd0e57f4f451f34965f02a07270f4a69f8968b6b71b391120534fc865fb7d94bc613668a3e9f8dd7138ce1cee5451f27346436b1f04a0ba28f8db0b1c280b7d651d13fc06d98bc125bc3cf289fe6f83c3a48adce3ab3cff27a55c4f8cedd46e9e7f90122e81a6369b83cf37c43d57105e1b2668269be1e42b54cf8d7f87334df295c597cc46b5ed2) (by decide+kernel)

private theorem block2:WideCovered band 7641053 8285772:=PRB band Z1.f2125 7641053 8285772 (WB 206366594135 32 0xb2cfa499bf202bfe6e4cb2cfa4003ee68dfe1f99b2cfa0f1bab992fdd0e5b2cfa0363a69f6fd8232b2cf9f733a2fa6fd337eb2bf9e8939d72efce4cbaebf9d8fb99516fc9617aebf9c5fb92edefc4764aebf9bcc3a45917bf8b0aebfa17bb9e00d7ba9fdaebfa00e3836c8fb5b49aebf9f6d37eff2fb0c96aebf9ec837bb44fabde2aebf9e03b76cf8fa6f2faebf9c34b589f07a207baeaf9b51b5527e79d1c8aaaf9b28b693d8f98314aaaf9a4eb6297ef93461aaaf9f29b5df56f8e5adaaaf9ea335a732f896faaaaf9d16b3e02a784846aaaf9c75339fd477f993aaaf9bccb36ec477aadfaaaf9b0e333b3c775c2ca69f9a2a32edd4770d78a69f992fb2b0ee76bec5a69f9806326406767011a69f9ce7b20f1876215ea69f9c70b1e56e75d2aaa69f9be5b1aa387583f7a69f9b55317c24753543a69f9ab4314baa74e690) (by decide+kernel)

private theorem block3:WideCovered band 8285773 8930493:=PRB band Z1.f1414 8285773 8930493 (WB 206366595160 32 0xc30fa4ec228810a2112f70bfe8f18892ee687f60ac2ffa290222040a1e9d5afbfe84b087cb168758a3beffa0d8a2eeaf21c27befbfe9fd08ae99086bb3cbeffa7312287c0219b222fbfe99ba898d64861dd5beffa586222ce32173c86fbfe926288178c85806ebeefa379a1c9fd214c6eaebbe892a8679d484e307baefa0d8215a49212514eebbe7d06849d508445a0baefa4e8a0d54e20fdbb2ebbe94a282d24883a838baefa464a0866a20d6612ebbe8e7a8195c4830ad1baefa2b020335720af076eb7e86e0803d98826d6ab6dfa08b1fd71c2087adadb7e7d167eb8d081d003b6df9ea1204d6a606053edb7e886c80664581329cb6dfa3449f016a2038fa2db7e8a5a7b7c24809535b6dfa1d49eb9992011a06db7e83d87a30cc7ff7ceb6cfa00d9e6b0b1fea46acb3e7bce78df487f5a67b2cf9dc19e11bd1fc2ececb3e712a7756747ebd00) (by decide+kernel)

private theorem block4:WideCovered band 8930494 9575214:=PRB band Z1.f2126 8930494 9575214 (WB 206366660728 23 0x6ba7ddb1be2445da486cbb4cfe20fbad90c1b22fb8fa67f0a7056b414590e060d33f81717b64086c8217ce99fcfe31df49eb23e964b3cbe2b2e341c2671e10579e5f10a19a127db8e6ac4cf2f82efabc83dd46e6aee797c526de8b862634bfd71c7e276fa58df0119251d8e3f155e12ac9c08c43dbc71f8a790947d9045fa93e38fc521549e73222e99d31c7e2805a4b29c116af818e1f137e5241c088b090dc70f89750914aa4455d2ce187c48d8480f94229ae9b0c3e22eb23d03011439e5861f1095d1ca96889ce3fc30f893aa8cd85044bfc5e187c4f2a46165e224c3630c3e26bca2d6a5111c449861f12efd157a88889371) (by decide+kernel)

private theorem block5:WideCovered band 9575215 10219935:=PRB band Z1.f1416 9575215 10219935 (WB 206366627864 16 0xdf6fa0b81eca2acdf8cfedafcf1ecf0dec66d50e36d7e6da376b17b356da3b6bf40fb39bd579a196adb5f9ee49c6dddccbe01edafce9cce194ce637a736d7e6b7d6efd7530826baebf2f853686a497a3ced74f9348dab58acb83336ba7c61bad3dfae59a3ff5d3e681967763d2b9731ae9f2f5b3325e3952e31d74f94685947d14a48656ba7c7c84cac3e24fcd8f5d3e188764a85126abf9ae9f25eef23ca892b895) (by decide+kernel)

private theorem block6:WideCovered band 10219936 10864655:=PRB band Z1.f1416 10219936 10864655 (WB 206366628888 16 0xe78fb5649719d5a97203f9e3ed9ff58cffaa52aa8e78fb44415947029235079dfec94e54749da3efdae77fafe9947ee928d49cf8dfeb5594f78eba2b50ce37faaead365ad6885e978dfeb4594b091ea17a3ee37fab4c12552fe83735f8dfea584479c3aa03f70e36fa796919934e7e88277dbe94f644987d9f04a2df6fa28450abd9a799cef7dbe97bb40e5c09dc9d4df6fa4925005b8a74b1b77dbe8b243edbad9c8f06) (by decide+kernel)

private theorem block7:WideCovered band 10864656 11186405:=PRB band Z1.f1416 10864656 11186405 (WB 206366661656 8 0xef7fa6afcfc15ed5561cbd6ff49665e4bba6a85783ae3e897339a68e54bc3cf5c7d02dd6eb616a8db12eb8fa0e2cd51003507b57d71f3ea419ae0869e8113ae3e76f7317d41d3816ef3c7ce302601cb1a66576) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 6029250 11186405:=(_Q1 band 6029250 6996331 11186405 block0 (_Q1 band 6996332 7641052 11186405 block1 (_Q1 band 7641053 8285772 11186405 block2 (_Q1 band 8285773 8930493 11186405 block3 (_Q1 band 8930494 9575214 11186405 block4 (_Q1 band 9575215 10219935 11186405 block5 (_Q1 band 10219936 10864655 11186405 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 16)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:16≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤46)
    (hT0:3264≤T) (hT1:T≤3300) (hnu:6029250≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤45454847903335488:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAF
namespace CYS
open AI AP AN
noncomputable section
def band:Band:=⟨17,18,4257,4372,1424574087666458⟩

private theorem block0:WideCovered band 2359261 6293060:=PRB band Z1.f1458 2359261 6293060 (WB 34399893527 1 0x38f35529600644) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 2359261 6293060:=block0
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 17)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:17≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤18)
    (hT0:4257≤T) (hT1:T≤4372) (hnu:2359261≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤1424574087666458:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYS
namespace CZF
open AI AP AN
noncomputable section
def band:Band:=⟨18,18,3938,4249,726263297292407⟩

private theorem block0:WideCovered band 2359260 6474295:=PRB band Z1.f1458 2359260 6474295 (WB 34399959063 3 0xe48b141f62ca37e48193594365b8e45f52ca33b2ca) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 2359260 6474295:=block0
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 18)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:18≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤18)
    (hT0:3938≤T) (hT1:T≤4249) (hnu:2359260≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤726263297292407:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZF
namespace DCM
open AI AP AN
noncomputable section
def band:Band:=⟨18,19,3806,4199,1445814988581091⟩

private theorem block0:WideCovered band 2490331 6655530:=PRB band Z1.f1458 2490331 6655530 (WB 34399959063 1 0xe5b053b4658e2a) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 2490331 6655530:=block0
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 18)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:18≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤19)
    (hT0:3806≤T) (hT1:T≤4199) (hnu:2490331≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤1445814988581091:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCM
namespace DAA
open AI AP AN
noncomputable section




open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DAA
namespace CYA
open AI AP AN
noncomputable section
def band:Band:=⟨19,19,3568,3762,5431712034038749⟩

private theorem block0:WideCovered band 2490330 6836765:=PRB band Z1.f2127 2490330 6836765 (WB 34534415479 8 0x8668b8e247ac0cd0a43bdcc057500cb9c79f3ba3198063c00d972b3a520f33007a800f5b8e640f286600f8001ea40c85ca90cc01ed003d08180246619803c60078ec2bdf514330072000eba44729b4) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 2490330 6836765:=block0
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 19)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:19≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤19)
    (hT0:3568≤T) (hT1:T≤3762) (hnu:2490330≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤5431712034038749:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYA
namespace DAS
open AI AP AN
noncomputable section
def band:Band:=⟨19,20,3423,3529,8208778260150074⟩

private theorem block0:WideCovered band 2621401 7018000:=PRB band Z1.f2128 2621401 7018000 (WB 206366695543 23 0x12433f794c89db2b9ac58424827e07e50753cd3548aec904fc4801f693826a0b2e9209f5dd03c5df24d309ff1c13e626a73b9c29a3fb3e3867ca6a0dd4079343c50470cf85bf9acb9de67f2708e19eec9633d812cced8831433d9938641d0599b98462827ac46cc0d777332ff14504f57b6977181a65d9b38a09e96992d77cdccaa7090c13cfa5c580f86993355218279c588aa96b3322392c304f334694d1cd263c0f585f9e548e28a01ecc6758d03f3c83e64f2c4698ad2581167006c000d3a0f11733827ce0086800eec161a8380559c00b80012519c137b208338017a00248f17a0c6c1067002ec0048da2d28cf820ce005a0008ef0498bb2) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 2621401 7018000:=block0
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 19)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:19≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤20)
    (hT0:3423≤T) (hT1:T≤3529) (hnu:2621401≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤8208778260150074:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAS
namespace DDD
open AI AP AN
noncomputable section
def band:Band:=⟨7,68,4061,4062,15999661226366636⟩

private theorem block0:WideCovered band 8912821 9889542:=PRB band Z1.f2129 8912821 9889542 (WB 206367581304 16 0xd34962300a86c564b738369a4b12a854057325966df4ce5893429efa992b98d1a672c48814f0104953f19d339623a0a754ee4a58e5e99cb116053a11d25091f34ce5887429d49f9272e5ba672c41214f2bc49309ded34961ed0a8297e493e47e99cb0e1853ee02e47bd034ce5860029f19b522c3e38611a3268ef9e3090d4a2bef8c6e91c36c1c47dd02e17c593c263844063a7d9efbe3151458eb9c118d4577dd186be1c41c108a34f0) (by decide+kernel)

private theorem block1:WideCovered band 9889543 10468339:=PRB band Z1.f479 9889543 10468339 (WB 206367479832 16 0xdb5974eacde309fbbf3db5974baca9c99f2ea4d7597482c75049ea155d7597452c3fb89e1406d7597412c09c49d86b8d75973dabd2dd9cf969d7597442ba0c49c6c1ad749741ab77f89bdecbd74973e2b4f939b517cd74973b2b27909ac42dd749737aafff39a36ded349733aad8be99a98fd34972faab1f4991c41d34972b2a8b90988ef2d349725aa659e9801a3d34971faa401a977454) (by decide+kernel)

private theorem block2:WideCovered band 10468340 11445060:=PRB band Z1.f570 10468340 11445060 (WB 206367479864 16 0xef997ab3a6fc85751a277ccbd69ce16b2b6229bbe25e94e4e86958dc11df12f367175d2ab536aeb89790b84813551c66f5c4bc1dbf30c2a478bfae25dcade7b55500725d712eb36f0f0ca6e8f4eb8972db7df2c52e72bf7c4b5e9cde18292cee7ae25d0adabdc3473237b6d2eae5bfdc4a27e7ddb69753adbdb050f897edb4ba7d6bda62858f836da5d52b5198941ad23b6b2ea35a24aea04942) (by decide+kernel)

private theorem block3:WideCovered band 11445061 12602655:=PRB band Z1.f479 11445061 12602655 (WB 206367513624 16 0xffc9727931be8701347fff25c824ae0b3bf3281fbc97199255e76f85f8feee5c4a47d1f9bcfd45fbb970e9197e6aef8aa3eee5c23451fd3bac80af7b970310f90fee6b5b7dee5bf242a761b892cff7a96fa105ed9adde0cbdea5bd4407a90b65d94f3a96efcfdeef6d50bdbcea5baa3e7d35b42858f3996e90f60c96cc36efce65b923cba83b1f31df3996e00efd432c361ffbe65b6c3b31deafbde1) (by decide+kernel)

private theorem block4:WideCovered band 12602656 13542460:=PRB band Z1.f479 12602656 13542460 (WB 240727251992 13 0x43fa5ec66f0af2cea43c85f4bd12d6d0e79b19070be979259e241731c79617d2f0e322173e5aba441fa5de66123f0ca3caa83ecbb68bc418d92441b07d976396d5d03201dbe0fb2eb22c70d8637668c0f65d3a567c94c5d23381ecba24a84c09896f2d03d973e14865ff0e73e20792e6b28167ee1412d3ff25cb54e48b7c167bc) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8912821 13542460:=(_Q1 band 8912821 9889542 13542460 block0 (_Q1 band 9889543 10468339 13542460 block1 (_Q1 band 10468340 11445060 13542460 block2 (_Q1 band 11445061 12602655 13542460 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 7)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:7≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤68)
    (hT0:4061≤T) (hT1:T≤4062) (hnu:8912821≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤15999661226366636:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDD
namespace CYN
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CYN
namespace DCD
open AI AP AN
noncomputable section
def band:Band:=⟨7,70,3952,3993,15543604759030708⟩

private theorem block0:WideCovered band 9174963 9803262:=PRB band Z1.f2130 9174963 9803262 (WB 206367745144 16 0xd749a29638539570e5657fb5d6689ac214fd1fe95059fd759a224e053e58f651d5074d26869c0148a4f493e4e2cf39a2d8c04e3452e4d520f3ce68b4fa13896d3930c54cf39a2ceb84e18c2e4b10933ce68b24a13836ab927bf5cf39a2c2a04df504e48cf1b3ce68af08137b6f391eb97cf39a2b5084de936e468d9f3ce68ab54137a023915b38c308db99aaaa431aa444c230c233ea0860e99e19082a9bef8c765e8b7d6c463d87b30be2ef5ecafb8a708e412e) (by decide+kernel)

private theorem block1:WideCovered band 9803263 10394603:=PRB band Z1.f483 9803263 10394603 (WB 206367643672 16 0xdb59ba3d95ac744f4df5edacdcff4acd1fe782e336d66e6cd5607973af65db6b372d3aae0f89ceacfd759b9109558264e2d386bacdc5baaa3d226f28475d66e12254bc99367367aeb36fa9aa3f7c9aa954d759b7be9506e04d0c7aebacdc4fca7ddf666225b5d66e12253b37731f071ae936fe029cf1b9867d9d749b77fd4dba8cbebbd6ba4db83ca6e0065d1c6f5d26d9a65356172d6d79ae936b63a9c07f96265d) (by decide+kernel)

private theorem block2:WideCovered band 10394604 11096821:=PRB band Z1.f2131 10394604 11096821 (WB 206367643704 16 0xef99bb7ddc2146aa54bd7ce66da44723148a83237f399a595dcb2a669c45e77de6f1c95c8a4aa5f0bcdf79bc25d6fd8529581777de6ef755b786aa4cffedf79bc2396b994a90fe837da6efad5a82cea3af41df69bbaa56826c28c7b8b7da6edb659a690a28e83df69bb26564aeea87f8976da6eb8b58c86ea16dc6db69ba935612a7a83759f6da6e91857e5f4a04d08db69ba3d95d8c627ef2a76da6e9ff57139c9f2c4a) (by decide+kernel)

private theorem block3:WideCovered band 11096822 12279503:=PRB band Z1.f483 11096822 12279503 (WB 206367677464 16 0xfbc9b507887226b76bd9ff77369a290972f2e8f847eee6d17ca0a5885c8ea9fbdcd9f53403dcdb7fc96f7b9b37067e618b6db7b1ef7366ad0f8d262d6ec6fdea6cbc81eaffcda4d2efbd4d943e3c8cbab379a0f3a9b216277790364b1c5e7536332cebb7c2c4e093cea6c6e79d20bcd80bb379ccd8ac039b356aef6a9f399b0eb67262755babd7df3360dace2fbd6b2d4bbbe66bf489c31c755ca3877ccd7809382defaa73b3) (by decide+kernel)

private theorem block4:WideCovered band 12279504 13462185:=PRB band Z1.f483 12279504 13462185 (WB 240727448600 16 0x87fcd826732f740e6b554c2fe6bec9d89c7033127ae17f35e770be5cb596525b0be9aebdf5c5e69ca087083f4d721bacd286e473d941fa6b72c95bf96f1f1bd60fd35af82a953898d4c6f07e9ad18e528047c5857a81ecd65b6a8313562325e40f66b1cc13951a70d0ffa07b358432993079844680ffd9abd054ae3ccc102837fecd5bf6249a3bdff0e2bff26ad4591e8d2efb0421ff93561b08c850f7b4094fbc9aac8d44e5c3bc7f8d) (by decide+kernel)

private theorem block5:WideCovered band 13462186 13904930:=PRB band Z1.f483 13462186 13904930 (WB 240761004056 6 0x22409b4cf040d1dcea16114481367ec07c0221d30e5d89026cc650edd35ba3db3f0dfcd923f9c867b743338a1bf9b180636c41967d612437f361d9669903ece8b67) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 9174963 13904930:=(_Q1 band 9174963 9803262 13904930 block0 (_Q1 band 9803263 10394603 13904930 block1 (_Q1 band 10394604 11096821 13904930 block2 (_Q1 band 11096822 12279503 13904930 block3 (_Q1 band 12279504 13462185 13904930 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 7)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:7≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤70)
    (hT0:3952≤T) (hT1:T≤3993) (hnu:9174963≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤15543604759030708:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCD
namespace CZU
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CZU
namespace DDR
open AI AP AN
noncomputable section










open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DDR
namespace DBB
open AI AP AN
noncomputable section










open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DBB
namespace DDB
open AI AP AN
noncomputable section
def band:Band:=⟨8,61,4122,4202,16497012708230383⟩

private theorem block0:WideCovered band 7995323 9493741:=PRB band Z1.f2132 7995323 9493741 (WB 206367777912 16 0xc718a2fb742b1a16921b9db8e3145e1a855e219241533b1c628c1c40aadb7647e657e384518018154d40c8f4490c708a2f7c82a720691d78e38e1145df2854af57238d14b1c228b95a0a8be3a46d619e384516d8c150be748d2414c308a2ce0429f03491937eb7df169176222309ce304f5aeba2b48ba2c153914581cc5d74536d222e50afa89f35bbae8a4d8f040dfe8511c63b75d1478f1065c64aa1f4b7ee8da0a711098f86cc36150831c5001880021e608281a9) (by decide+kernel)

private theorem block1:WideCovered band 9493742 10051292:=PRB band Z1.f541 9493742 10051292 (WB 206367676440 16 0xcf38baa58b9afb6657b733ce2eb8dae220c98d6bdcf28bab14b7c23a613a7b3ca2e9dcadb42c97c67fcf28ba410b608f65cf9833ca2e8062d445d96b641cb28b9c5ab445fe58b88b2ca2e5fb2cd14095a603cb28b93aab272aa5477932ca2e66c2c59be9495c5cb18b9698b0c62250369b2c62e4bb2bfe24938587cb18b8f76af586a4bf5a72c62e2e12ba74992754ac718b8754ade59647b4af1c62e0c0ab515791650c) (by decide+kernel)

private theorem block2:WideCovered band 10051293 11061853:=PRB band Z1.f541 10051293 11061853 (WB 206367709208 16 0xe768b1d957b206b5194bbceb162f42f313da9ee87f8d62c44dddfcf2d354f0f1ac5850d3b2ccba599a3e358b0c3d750cc14912cbc6b160d6ce7d4ea8de4a38d62c0281cb7e45134756fac57d31b9246ca158acdf48af1b57173494090ddbe915cc12e18c227ce0c37d22b5119c1a9e4f13f96fa455958386bab9d17b4e358a4c397491b1380eeda6715b66abcbeda6bdce73ce2b64c9775654d378d679c56b9a2eaa3199e6fb) (by decide+kernel)

private theorem block3:WideCovered band 11061854 12176955:=PRB band Z1.f541 11061854 12176955 (WB 206367710232 16 0xf778b8a5252ae06b9ce3bf378b7fdd50c0b1b8bdfdf388b75664ed8cbb7adbff378b6f314d1e0cb69d81f378b667f4b8d6bb58d43ef78b5dc04a0083b47d06ef78b54df487499b36cc8ef78b50b8471831b25c8aef78b49da45efb9b14c4ceb78b42ab44bf89b03c0eeb78b3af3437d9daf2bd0eb68b3851425c8fae1b92eb68b31f34158fdad0b54e768b2b5b4055dfabfb17e768b246d3f511baaead9e768b23383e5ceea9da9b) (by decide+kernel)

private theorem block4:WideCovered band 12176956 12455050:=PRB band Z1.f541 12176956 12455050 (WB 206367710232 4 0xfb68bb52c5b445ebe0c8af768baa7e594891bcfef5f768b9dc556e42ebbeeb7f778b94d854a3b6bade79) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7995323 12455050:=(_Q1 band 7995323 9493741 12455050 block0 (_Q1 band 9493742 10051292 12455050 block1 (_Q1 band 10051293 11061853 12455050 block2 (_Q1 band 11061854 12176955 12455050 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 8)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:8≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤61)
    (hT0:4122≤T) (hT1:T≤4202) (hnu:7995323≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤16497012708230383:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDB
namespace DBE
open AI AP AN
noncomputable section
def band:Band:=⟨8,62,4060,4172,18813173729294498⟩

private theorem block0:WideCovered band 8126394 9465473:=PRB band Z1.f2133 8126394 9465473 (WB 206367776888 18 0xcb18c4208c54ed87641ba071c63103eb15274258fe4dac718c3fd30545edd63d6ccf1c630f9de1508ecd8ed18cc718c3cd5c53ec616391f971c630f51014e14358dbe3ec718c3f0d05351bb634d25f1c630fc7414ccdd58caaf1c718c3df34532851630852b1c630f23514caf9d8b97a3bae8d1d68d5112d522c37f2eba325fc92d2f39c89faaebae8c6c6307fa32b2239d82eba315373192388c87d412bee8b6a559cfb302e1b0312eb62159821b0c49a849a28b6c8629aac335fe2609ce3413630034d006deb0804cf1) (by decide+kernel)

private theorem block1:WideCovered band 9465474 10029296:=PRB band Z1.f545 9465474 10029296 (WB 206367709208 16 0xcf38d272d5aefa33211e19e71a4838b4f23e61fd273ce348d4567b7acbfad1679c692a8acc068976bfbcf28d22e95923f72dc4a99e51a40c4b18e2a5962b73ca3476d561a894ae783659468d41abf93c954560cb28d176e5793372977739651a2828ae65ca50c84b2ca3441955b44e49d435e59468a792b36c3931ec4cb18d14aa5609e7252a3b9631a23f6ab8886482ddb2c6343c495600ec8c0e7e58c685f0aa9efa90f828) (by decide+kernel)

private theorem block2:WideCovered band 10029297 10945507:=PRB band Z1.f2134 10029297 10945507 (WB 206367709240 16 0xe768d804276954ca703e3e768d781475817ea5f096e368d6ee6748608a4dd48e358d626c7321aaa3c9fae358d54887258bca2b6ace358d61bf715a3ca1a35ee358d5839713ff6a09010e358d4a237117629f7cc2e358c7c6d73a1f69e6974e358d08bf7069019d5627d348d33035db9869c42d9d338d34ab5d417c9bb932d338d323f5cd13e9b2f8bd338d2fbc5c60889aa5e4d338d2cd15bd7a89a1c3dcf38d2a115b644c999297) (by decide+kernel)

private theorem block3:WideCovered band 10945508 12073153:=PRB band Z1.f545 10945508 12073153 (WB 206367743000 16 0xf388d050926c3b0dc1c60f9c467f4012f9e6adc95d3ce233e85e944a7b6c244de7119e95c48d23eb4fed8ef88cef39a3c1ff59f5c577c4674839181cb6cb60f3be2339a4e898af16389dddef19c2dc438eb9b0b1a0eb78cdcbaa1427bd7cf2975bc66b9f90534baba2c17ade3357b0808bd75aef6fd6f19a3eb3f763aac6469eb68ccd419f3ee455a88df3b4664700f6ce12a8f7379da330ddc796cf95254ffced1988de3c0847a81731) (by decide+kernel)

private theorem block4:WideCovered band 12073154 12636285:=PRB band Z1.f545 12073154 12636285 (WB 206367743000 8 0xff78d42a02f6dfae0683efdbc69ccdd71e55afeff8bede34bf90b3cda77d5929f711a51b9576c2cbd9946fb88d20e1aaaa7e5e42fc7bc468c7dd4d23e2edcaafde2344af4a214eb74bebbef11a186c4f5e83b94c0f) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8126394 12636285:=(_Q1 band 8126394 9465473 12636285 block0 (_Q1 band 9465474 10029296 12636285 block1 (_Q1 band 10029297 10945507 12636285 block2 (_Q1 band 10945508 12073153 12636285 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 8)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:8≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤62)
    (hT0:4060≤T) (hT1:T≤4172) (hnu:8126394≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤18813173729294498:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBE
namespace DCF
open AI AP AN
noncomputable section
def band:Band:=⟨8,63,4001,4141,20393803666031911⟩

private theorem block0:WideCovered band 8257465 9397653:=PRB band Z1.f2135 8257465 9397653 (WB 206367810680 17 0xc718e27fd214dbd4c8f6595c718e2720014cc4c48eda67c718e2615814bd9548e4f38c718e24ca014aff348dc409c718e243fc14a3df48d38dac718e2475c149a3748cadabbef8dd51ded948d338c227cbae8cb60ea54d0b028b0c1ebae8c60e4e2d794aa89f5c1bae8c44e4420010ea88df63bae8c36172194a26a87c905b6d8c2bee414b655286b2a7b6d8c245b011566da859c4ab6d8c205d20f30fba8485ecb6d8c1cf500db92c2836f8eb6c861b1440d36199825930aeb820f94e077f370802c74) (by decide+kernel)

private theorem block1:WideCovered band 9397654 9967748:=PRB band Z1.f545 9397654 9967748 (WB 206367709208 16 0xcf38f6a4c58fb693031099e71eddfcb106225e355b3ca3db31d60867cb8113e7947b4c52be0dc9676f8cf28f661d57617b2bd7939e51ec4eaae016255826b2ca3d7a1d5a7c04a6ab5e5947ad222b1e07944a3ccb28f559655d761277e1b9651ea240aae0de4ccf7b2ca3d6af154347495457e58c7aba52a6246921d80cb18f538f547d312324a39631e9ef0a86e7e441c8b2c63d2bb54fcb3c83df9e58c7a2e6a9d80a8ff0c4) (by decide+kernel)

private theorem block2:WideCovered band 9967749 10751628:=PRB band Z1.f2136 9967749 10751628 (WB 206367709240 16 0xe368fc2d672f3b0a40e8ce368fb1ca72112ca2f82ee358f9aa17162a8a1e1d0e358f7ba5711842a0cb72e358f2e7871d4449fb515e768e2d7476c2f39e9eb7d348f87535dd8769d8859d348f83825d4a969cfd2ad348f7f845cba2e9c71fbd348f82f95c2aac9be6cdd338f7fdb5bb6c69b5b9ed338f7ca15b42329ad06fd338f79465accbe9a4540d338f75c25a560c99ba11cf38f720f59ddb8992ee2cf38f6e40596a4898a3b3) (by decide+kernel)

private theorem block3:WideCovered band 10751629 11891817:=PRB band Z1.f545 10751629 11891817 (WB 206367743000 16 0xf398f359ea4499d5aba34f9c47975f51d136ad1782fbe23c9f6a8bfe01668f5bdf11e40ad449f72b2314fef88f1d8321b0c9588d7977c478ba95091adac01253ade3c43b8825a2f5ddc6dd6f1e147740123badd7d8eb78f08e81f8648d660bdf5bc781ba8f8bbceaeac779de3bf6da7aa70355297fced1def0d3c7866a97e61e768ef31f1dcdd754340273b477956cebc2629d469b9da3bb76c74ea4d4c7691ced1dd09239fb5fa524ea) (by decide+kernel)

private theorem block4:WideCovered band 11891818 12817520:=PRB band Z1.f545 11891818 12817520 (WB 206367743000 13 0x1ff11f6ee865e06fc39470ff88fa8ef3166c8614067ffcc7cf2857fc82705a9c7fe63e446cba4b0f80a827f731f08505a6c98bf3db5fb98f7a612be267df13ac7dcc7b7e055638eef443ebde63d9506a6c7f177f539ef31eb5a15142e8bae43ef798f541927a26b5ce6f0fbcc7a5bb5361e12e2de0fce63d0b4697a0236f424be731e742d4a1bd0b68ac7) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8257465 12817520:=(_Q1 band 8257465 9397653 12817520 block0 (_Q1 band 9397654 9967748 12817520 block1 (_Q1 band 9967749 10751628 12817520 block2 (_Q1 band 10751629 11891817 12817520 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 8)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:8≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤63)
    (hT0:4001≤T) (hT1:T≤4141) (hnu:8257465≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤20393803666031911:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCF
namespace CZG
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CZG
namespace CYW
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CYW
namespace CZW
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CZW
namespace CYR
open AI AP AN
noncomputable section
def band:Band:=⟨8,67,3777,4012,21418250682550398⟩

private theorem block0:WideCovered band 8781749 9358331:=PRB band Z1.f2137 8781749 9358331 (WB 206367843384 16 0xcb2961fe40099f18b1d97f79652c3f026133c76e3a0d532ca587c2d4266cdcc71d56e594b0f48684cd8c38df205cb2961dfd509989e71b52bd9652c3abea13331b63582db2ca58727ac265fb8c68c07e594b0de4304cd3a58ccf67cb2961abd8099a43b190d819652c330c2133eea630f8632ca585fd282687a1c5fab8df7c6be65a31d5d228bacc9bae8c72f7c1e4eba115145775d1884aa422a6ed2259e3aeba30cf810368bc14422785b6c6142378556872872252) (by decide+kernel)

private theorem block1:WideCovered band 9358332 9897714:=PRB band Z1.f2138 9358332 9897714 (WB 206367742040 16 0xd3497233ea9f60425c1bcb4d25c8fd4a744409675a3d33971fa229b7cb25791534ce5c6ad8a68710955306d339714fe298fed25306df4ce5c38b6a60e70943068d339705cc297ef124e7c674ce5bec50a61670930dcbd3396eca6299e14249f1f34d25b5f2aa753c491eb2dd3496b47fa9d375e45677b4d259de26a72f9690c88fd349655c2a9d5da640dd032ca5c1d289a731c8fa5f1cb29704bd268f9023d752b2ca5c08ae9a27ac8f14a2) (by decide+kernel)

private theorem block2:WideCovered band 9897715 10492896:=PRB band Z1.f562 9897715 10492896 (WB 206367741976 16 0xdb5974bcf2d2682a01be0db59748922ceaed9f8a91db597452b2caf009ef942d75974191ac729a9e67f3d75973dbc2c357a9dd6a4d7597399c2bf75f9d4555d75973b52abb7ea9cb406d75973c5b2b80de9c22b8d749739672b5a079b9169d749736272b30aa9b001ad749732832b02ff9a6ecbd74972e8eaad5ab99dd7cd34972a342aa8a3994c2dd34972558aa7bd498baded34971fd52a4f2598298fd34971f6aaa2296979841) (by decide+kernel)

private theorem block3:WideCovered band 10492897 11385668:=PRB band Z1.f2139 10492897 11385668 (WB 206367742008 16 0xef997ad8c3cb56856dda277ccbd0b3ddf619ab2629bbe25e9a9ced1f2d56ec11df12f369975af0caa536aef8978dca3a8667549866f7c4bbe321d33d72a038bfbe25d98e8ecae5d4dd725df12e693176f1c5a5c8f4df697602baf5a0652532befb4bae73d7895fa9054237da5d661ebb2c35470773b6d2eac0c5d0580a2f26adb697525dae399d51308dedb4ba742d6f7b22873f336da5d3a5eb68f09427cfbb6d2e9dd15ac3c2a0ad2f) (by decide+kernel)

private theorem block4:WideCovered band 11385669 12576031:=PRB band Z1.f562 11385669 12576031 (WB 206367775768 16 0xffc9736e0d4a1aeeff947fff25cc526508bebbec281ffb9728dbd3aabc6f67f8feee5c80af4cc189bc7d45fbb97176312b7486ed6aa3eee5c4e2f494044ba380afbb970c5711eefdee455b7dea5c13f4463b2db7f2cff7a96ffea112ebaadb40cbdea5bee294381deb5ad94f7a96f5585094fdad22bdbcea5bbc654137b9b36858f3996e8dd900e722c916efce65ba2963f36f4b1231df3996e32e4f96a0ec001ffbe65b75343d84b9aedde1) (by decide+kernel)

private theorem block5:WideCovered band 12576032 13542460:=PRB band Z1.f562 12576032 13542460 (WB 240727515160 13 0x87ecbff046848523cea43c87ecbf34ba7ec239cd848385ecbe75c878e4d4cc61e585ecbdde8e738964cb3f4885ecbd55666f619aca1caa83ecbcc6d06b0fdac8fa0d83ecbc3d9866ee84c7d76f83ecbbde60635c37c6b4d183ecbb708a60167ec5923381ecbb057e5ced1cc46f9681e4bab83259f19ac34cf881e4ba61605768ecc22a5a7fe4ba0be054f145c107bc) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8781749 13542460:=(_Q1 band 8781749 9358331 13542460 block0 (_Q1 band 9358332 9897714 13542460 block1 (_Q1 band 9897715 10492896 13542460 block2 (_Q1 band 10492897 11385668 13542460 block3 (_Q1 band 11385669 12576031 13542460 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 8)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:8≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤67)
    (hT0:3777≤T) (hT1:T≤4012) (hnu:8781749≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤21418250682550398:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYR
namespace CYM
open AI AP AN
noncomputable section
def band:Band:=⟨8,68,3725,3978,20947737827292686⟩

private theorem block0:WideCovered band 8912820 9401501:=PRB band Z1.f2140 8912820 9401501 (WB 1305879471256 16 0x6794c0eeef84d41c511ee93acf2981d26309a903e23cacc99e530386661355fdc4770e333ca606ba0c26baa688e985b679cc0c8bd04da63511c9ddecf39815ad109c383a23816119e730236e413a47e3c6de0c33ce6040b1c273ec768d72ad679cc06f2884e7d30b1a5282cf3980c1d509cb5012337f5b96730113961399b71c64b3532ca606ddd425ddf528c4cff5f7c6c9c3e30126723180728bef8d173b94315e9822dc2f575d18d86643464e00452587aeba310d6f44098020892561) (by decide+kernel)

private theorem block1:WideCovered band 9401502 9815000:=PRB band Z1.f2141 9401502 9815000 (WB 206367742040 16 0xd7499103029c7852570f635d263fed6a7d008953102d7498e67e2a1a2c25278af5d662f5c8a9b1b7940b54d749888472a5b10a4de1f75d2618904a9536992e5a6cf3991f43a6ded02494b3f3ce64713a9b4694920964cf399195aa6ce1c246ffe33ce6457689b0a1091768dcf29911ff26b7a7244b4873ca6436de9ab6b090e3b6cf29908eca6a4be242692f3ca640e069a74649050e0cb298fd4ea696fc2401dd33ca63d9f29a851c8fbe09) (by decide+kernel)

private theorem block2:WideCovered band 9815001 10416453:=PRB band Z1.f479 9815001 10416453 (WB 206367741976 16 0xdb5995ce22c0ab09ef145db5995918abd4949e5e6fdb599550eab9e579dcb98db599512dab77219d38c1d75994c78ab410f9ca5ead75994749ab0a729c1313d759941802ad3029b803cd7599429aaaaea39aed65d759947bbaa76039a5a8ed759944a6aa4e5699c7b8d749940852a3b1b9934e1d74993b5aaa19f898a20ad7499357729fb09980f33d74992f3ca9f4f5977c5dd7499271929df1596e986d74991d1029cf0f9656af) (by decide+kernel)

private theorem block3:WideCovered band 10416454 11093088:=PRB band Z1.f2142 10416454 11093088 (WB 206367742008 16 0xf39997723bbc79254a23079ccc975d1e9891ea07acb8de660762bef7014df20bc6f32fc795ef374a6662edf7997a122f283952e9abefbccbadc576ac6a9502037de65c678ba3f99495b53bef32eae15c7bf8a41ad2df69971e22dfae351c3fdefb4cb74996e1d228bd4977da65aafab6024144c49db6d32cd695a78aaa1cf77db699626e2cf723509e506db4caf2c565fe8282a72b6da6572c0b1e219402de7b6d32c02158689a9f841c) (by decide+kernel)

private theorem block4:WideCovered band 11093089 12295995:=PRB band Z1.f479 11093089 12295995 (WB 206367775768 16 0xfbb992bfb126b046ee7cefeee648a3d47dec9ba798dfbb991f9b119e832e54f83eee645f85450a35b82e32f7b9910d250f5826dc2213dea6425d142a6e2b5e2d6f7a99079d5055dd2d2f4a7dea6406da4073f0b3977bf3a98fa918fd7b3ec9c737cea63cf293e8ae3b14c1ff3998ec34cf707c2c099cbce663baaa3cdb99af00c4f3998e8ec0f19912b76c5bce66384f73bc491acb568f3998d9214ee45feae3eefce66339333bab30aa6a0d) (by decide+kernel)

private theorem block5:WideCovered band 12295996 13498901:=PRB band Z1.f479 12295996 13498901 (WB 240727546904 16 0x87f4c80e137b0c02cdfa1587f4c7b27875ec00ccd46785f4c7546470a8c7cbaeba85f4c7107a6c2562ca890c85f4c6c65568092ac9635e83f4c684a36471dfc83db083ecc644ed60fe6ac7180383ecc6157d5da84cc5f25583ecc5e2535aebf8c4cca881ecc5ab4e57fad1c3a6fa81ecc588da556bbcc2814d81e4c56025534dcfc15b9f7fe4c533a650fd3cc035f17fe4c50b5d4ef7a9bf10437fe4c4f1dd4cdd87bdea967fe4c4d0fd4b4056bcc4e8) (by decide+kernel)

private theorem block6:WideCovered band 13498902 13723695:=PRB band Z1.f479 13498902 13723695 (WB 240727547928 3 0x44fa64af4123b519b45a0be1fd323a0c5104d89a08ae10fe990cef880dbedcf1fc2) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8912820 13723695:=(_Q1 band 8912820 9401501 13723695 block0 (_Q1 band 9401502 9815000 13723695 block1 (_Q1 band 9815001 10416453 13723695 block2 (_Q1 band 10416454 11093088 13723695 block3 (_Q1 band 11093089 12295995 13723695 block4 (_Q1 band 12295996 13498901 13723695 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 8)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:8≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤68)
    (hT0:3725≤T) (hT1:T≤3978) (hnu:8912820≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤20947737827292686:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CYM
namespace DCS
open AI AP AN
noncomputable section
def band:Band:=⟨8,69,3675,3943,24202393185243491⟩

private theorem block0:WideCovered band 9043891 9423719:=PRB band Z1.f2143 9043891 9423719 (WB 1305879471256 16 0x69a4d0739c84f78adb1f96ced349a0c66409ea1e723e04e39e73425cdc1381435c79b8433ce68727742645ffa8eecd9679cd0d43a84c888131d4552cf39b3c5a661e997623961e99e73672c52d38bb2bc70725b3ce6c1e85199629968dc41c679cd6303e32558e2b1af3d8cb29b96ad9675fd7d234bef5965371979ccd5cd224672c6b2ca6e29039a13b5f38c9b5e6594dbff8434361c2518a25cbef8db688c615a1586301bfd7df1a930c8927e75845de67aeba3311c48b03f2d08b2870) (by decide+kernel)

private theorem block1:WideCovered band 9423720 9727581:=PRB band Z1.f2144 9423720 9727581 (WB 206367742008 16 0xd339b2da62713e2ca372ee99cd94d793850465090bb3ce6c953e9c053327b3fd9e73640334ddcc1938fcfcf39b1bffa6e78ec9a2cfe79cd8cc5537142e4bedc33ce6c59bc9b7e672562839e7362b104da267926712cf39b1121a6d1cfc90e71679cd8577d36bed6474acf3ce6c09e69b8f772311079e735ed3e4df0a5913e54cf39aedd526fd1ec87a12699cd6b1f539645642a7d74d26abf709df12720bf8da69350d814f810e901597) (by decide+kernel)

private theorem block2:WideCovered band 9727582 10297323:=PRB band Z1.f2145 9727582 10297323 (WB 206367742040 16 0xdb59b63f9aaef052747faf6d66d7c38ab07109c8b8cdb59b5a2eaaa6b426fdcbb6d66d5078a9f0689b62cfdb59b4dd82a673126b39c36d66d18b0a930c49a3a11db59b3cfcaa35b726696cf6d66cc830a8d094991154d759b22fdaa1e97261f3d76d66c3e68a8ea0497e896db59afea02a472225d50e36d66b2780aaf31496bfd9db69a90e8ab0d44a58adeb6d669ad08abdb9595971bd339b34a4a72bfc2540af34ce6cc50e9c7a9094b88d) (by decide+kernel)

private theorem block3:WideCovered band 10297324 10905048:=PRB band Z1.f483 10297324 10905048 (WB 206367741976 16 0xe379b9288aeaa54a665d8e379b8e37ae5e40a5d179e379b8a2cae1f02a53d1bdf79b85efaddfcaa4a8bcdf79b80f72d915ba4145ddf79b7c30ad50e9a37ffedf79b81932cff42a2eba0df69b7e6a2cccf1a25741df69b7a38ac8e9aa1c2e2df69b76422c5e03a12e83df69b7189ac1f31a09a25db69b6cfa2bef51a005c6db69b67ec2bbd149f7167db69b61fdab7fc39edd08db69b628bab50eb9e48a9db69b6801ab0e689db44a) (by decide+kernel)

private theorem block4:WideCovered band 10905049 11930584:=PRB band Z1.f2146 10905049 11930584 (WB 206367775800 16 0xfbb9b18f91071dbd6c17b1ef73621d8a058852d38c6fdea6c22e13f9d8159dd2efbd4d84edc7d6c6eb291a0f7a9b02f98f7eae162d1c5ef535f7639eb40a2c10093dea6bcea33d0fb5578bb379d4d744a2795722adeea9f3a9ad9184f22319598bd7e75357eb01e7a992ae74bbdea6a0d303f143ed53a3871c4d680fe606866a94bb3e389acded8bf99f1516ea9c713596ca17c4d32a08bd78e26b2f422f3a1053c74b71bcd659105dd2e0a6fa37) (by decide+kernel)

private theorem block5:WideCovered band 11930585 13146034:=PRB band Z1.f483 11930585 13146034 (WB 240727514136 16 0x85f4dda0f4c3ae31912f6507e9ba3c497a2fb31dbbd60fd3728032db4ab63231bc1fa6e2b4d58d331c51d7a83ecdbef32ac938187e97903d9b711e14f43bb0b2ffa07b36cc61a8b1ed60d1a040f66d78774f6005c07a8381ecda9dbe9ae0ff7ea38affc9b493b92e2296f8a421ff93687da24da455e80253ff26ced6d48306abbd78d7fe4d99ce08dd727755d9efbb9b2ab7515e14ee61845f77364f9a2202dbdc2ea9beee6c822842e343b73496) (by decide+kernel)

private theorem block6:WideCovered band 13146035 13904930:=PRB band Z1.f483 13146035 13904930 (WB 240727547928 10 0x22ff36bb95d36a357a8584513f9b499b492c4d6d3065d89fcd9ac7045238a68eecfc4fe6ca0aea0f302b42d38a1ff36328acfb17cd9f18490ff9b0afe6779497ce636787fcd802d1392bc4e69d54c3fe6bd50e9b702e73047ae17d35d54c0d2c6fd95d25b0be9ae27c06543e6c9c070) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 9043891 13904930:=(_Q1 band 9043891 9423719 13904930 block0 (_Q1 band 9423720 9727581 13904930 block1 (_Q1 band 9727582 10297323 13904930 block2 (_Q1 band 10297324 10905048 13904930 block3 (_Q1 band 10905049 11930584 13904930 block4 (_Q1 band 11930585 13146034 13904930 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 8)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:8≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤69)
    (hT0:3675≤T) (hT1:T≤3943) (hnu:9043891≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤24202393185243491:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCS
namespace CZS
open AI AP AN
noncomputable section
def band:Band:=⟨8,70,3625,3879,24157628611101568⟩

private theorem block0:WideCovered band 9174962 9481960:=PRB band Z1.f2147 9174962 9481960 (WB 1306953213080 16 0x68d2705271c27133bb90aee868d27045ff4273364a9063f568d2703ea38272be4990190268d27034490272ba788fce0f68d2702a4f827222c78f831be7ce7031c6426c78268f382866ce74addb95d9c0358eed3466ce74bbf9d71a1a458ea24166ce74e21ad95222858e574d66ce748f93d9dd6d148e0c5a66ce73e931d9a9a9538dc16664ca761ee39997f6d28d767364ca7600e4997ee3528d2b7f64ca75ea86d99918128ce08c64ca75d279d9c60cb18c959864ca75abe219d712708c4aa5) (by decide+kernel)

private theorem block1:WideCovered band 9481961 9788958:=PRB band Z1.f483 9481961 9788958 (WB 206367741976 16 0xd349d283e26cd03955e1ed349d2555a6c12895132bd349d222ca6b59894c838d349d1e9b26a65b947d45d339d1afd26a186943251d339d16b02693b793e75ed339d1220268e64939c6ad339d0cdf268638935177cf39d06cc267b9b930683cf39d0031a6803392bb90cf39cfb8aa6799892709dd339cf46526843f9225aad339cee7da6868891dab6d339ce735a68b8d918fc3d349cd6ada6aeca9144cfd349cc6f426c7ca90f9dc) (by decide+kernel)

private theorem block2:WideCovered band 9788959 10402955:=PRB band Z1.f2148 9788959 10402955 (WB 206367742040 16 0xdb69d4e83aafaa5a7af22f6da7531b0ab26169e26a5db69d4fcb2a98bba7642fb6da7542c8a9b94e9cfad7db59d4bc2aa3f86a7193c36d6751b50a88c2e9bcf0adb59d4145aa09fca6ce48f6d674eb88a7d4ee9aa33cdb59d335c29e626a6835576d674a60ea713a299776fdb59d1df629c3f5a6386236d6743b34a74d62984ba1db59cf993a9fc50a5ed6eb6d6736462a95166971fd3db69c9da7aa704d65a27b36d671dfe6a992bc95f405) (by decide+kernel)

private theorem block3:WideCovered band 10402956 11016952:=PRB band Z1.f483 10402956 11016952 (WB 206367741976 16 0xe389d818baef5d5a81af8e389d80912ea3aca78512e389d81312e5a19a6ef2be379d7d842e190fa65944e379d79b3add820a5c35de379d75462d8955a52d77df79d7114ad479ea49790df79d6ca62d0579a401a9df79d67ecacc2c1a36bc2df79d69cdac7f25a2d5dcdf79d69e12c36e8a23ff5df69d6628ac03cda1aa0edf69d6238abd153a11427df69d5e042b9f66a07e40df69d597c2b6e189fe859db69d5401ab2c1c9f5272) (by decide+kernel)

private theorem block4:WideCovered band 11016953 12168196:=PRB band Z1.f2149 11016953 12168196 (WB 206367775800 16 0xfbc9d1d1e1140559735809f773a2984a1d9e5ae200dbeee744c0e425c875baa34fddce862be82c9ceb6289bf7b9d054f101e65969f99def739f9099fa8e82cf4403dee73eb833e78b25952997bd4e7b9b67b3b18b17964f7a9cf0a14f49965609b2fef539d2029e6b68abc8727dea7377ea3c5db756fafe7bd4e6831a7946ecacca2ef7a9cb8420f5bee9573cc3ef538f49a9f1cb3ea9ca4f9e27315a82fa4e554a36371c4e619b65ea49ea8b0df) (by decide+kernel)

private theorem block5:WideCovered band 12168197 13396190:=PRB band Z1.f483 12168197 13396190 (WB 240727514136 16 0x87fceec3e4dbf60b98d1bd0bf9dc4b89a70c2f2cf44217f3b636c32dea06508a1c2fe768d9e61e452c8e57585f4eca288bd7ba78f735107e9d8436d6d854f1a376a0fd3af4352c411162b10641fa75b91c561b68c4363e81eceb0b68a6fee78614e303d9d55d4d44e5cf077a8e07b3a9e672789d560596b40f67514c44d223dbf87087fece9de0a96c03f7cb676ffc9d310952582baf4bdb5ff93a5bc0a3f5125e01cfbff274987946918ebad7d1) (by decide+kernel)

private theorem block6:WideCovered band 13396191 14086165:=PRB band Z1.f2150 13396191 14086165 (WB 240761103448 9 0x131f4ea37143380dd2d6f0159aa273521ef04c6d6eae3a545813aaeb489e97eb3526df22409d425e64aa87e9a6df5f1204e96da9230bcc0d243e18902747c1c909c158688c0a44813a215f87e9d9933fb11a1c09d0226e3c22c019d80f30dfce7bbe21cb5f58cd94ab) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 9174962 14086165:=(_Q1 band 9174962 9481960 14086165 block0 (_Q1 band 9481961 9788958 14086165 block1 (_Q1 band 9788959 10402955 14086165 block2 (_Q1 band 10402956 11016952 14086165 block3 (_Q1 band 11016953 12168196 14086165 block4 (_Q1 band 12168197 13396190 14086165 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 8)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:8≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤70)
    (hT0:3625≤T) (hT1:T≤3879) (hnu:9174962≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤24157628611101568:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZS
namespace DBF
open AI AP AN
noncomputable section








open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DBF
namespace DAK
open AI AP AN
noncomputable section








open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DAK
namespace DDM
open AI AP AN
noncomputable section










open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DDM
namespace CZR
open AI AP AN
noncomputable section
def band:Band:=⟨9,56,4124,4261,10313480134692771⟩

private theorem block0:WideCovered band 7339967 9226631:=PRB band Z1.f2151 7339967 9226631 (WB 206367709272 23 0x617c1aee5aced8ee33261f0be0d69396611871887117df06ac76b2344b8bbd89bef8351e458b609c59bc55f7c1a6a1ac2e4be2ac62efbe0d265d5f6ecf1457197df06a66eaf057789a58dbee834f8757286bc48fc75f741a5faab75c5e22663efba0d1ed55a75d71027217dd068618acae2f878d91bee833df2562157c383c95d7419baf2ae29ae1a064eeba0cc0b55654f70bf72975d064d18aa6bd7857595bae831b09550e9bc277cb5d74190682a6445e11a65eeba0ca10152485707c73175d063d5ca9319f835d99bae83263c5458c9c16bcd035c1011600776fa09466c192080570021ecb0397380d50401d200a86480bf9e) (by decide+kernel)

private theorem block1:WideCovered band 9226632 9775479:=PRB band Z1.f1161 9226632 9775479 (WB 206367709208 16 0xcb183850b619bcf2a52ef96307037ec237a2528de31c60df79581ffd4a0ebce38c1bd242ffe0493977ac7183762a5f61fb2622f78e306f480bda5d64a2df31c20ddd8579a61c902bee3841ba00aef39e917f7ec708370de5d7c5921f2ff8e106da50b9ebfe41ce030c20da6997221247f6c0e1841b2cd2e02c98f6782c308361675b88e91dc30786106cc4eb6273a396e130be0d91f16a884c6eac2e17c1b0b9ad26148d4f86) (by decide+kernel)

private theorem block2:WideCovered band 9775480 10838872:=PRB band Z1.f2152 9775480 10838872 (WB 206367743032 16 0xdf3830c19a1bfd32958d637ce0c193085314ea4575adf382ff4520c08128d2d737ce0bff66813a16a23f5edf382fa559fe690a84cd836ce0bd1507dffa8a02762db282ed919f19cba7c6d936ca0b97807af0e69e0f66db282eb7c9e84ad2740da36ca0b9732792e489bf76adb282df021e1e0126badb36ca0b5904780b2c99df6edb282c98f9e09f3a634dc36ca0accb87987ec97c772db28273551e13eee5aedd32c60b11346232da95af76) (by decide+kernel)

private theorem block3:WideCovered band 10838873 11730110:=PRB band Z1.f1161 10838873 11730110 (WB 206367743000 13 0x1de706c805574b92b2fcbeeb3835bf9aad02dd8f9a0759c1a8f614df986c39d0baca0d2ff0a310615fb689d650687794fcdd8aecf46e72833b6c270bb5d6e1a473941998a931a5a2b2dd2b9c60cbf5c9611f7575699ce50651de49aa23aa9f4ee338321dea4265ad4c9a8719c18d46d1bb752a21d4b8ce0c60508b43dd4ef6a9c67062444448b92a66f56) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7339967 11730110:=(_Q1 band 7339967 9226631 11730110 block0 (_Q1 band 9226632 9775479 11730110 block1 (_Q1 band 9775480 10838872 11730110 block2 block3)))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤56)
    (hT0:4124≤T) (hT1:T≤4261) (hnu:7339967≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤10313480134692771:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZR
namespace CYL
open AI AP AN
noncomputable section












open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end CYL
namespace DAO
open AI AP AN
noncomputable section
def band:Band:=⟨9,58,3992,4205,24266187225847908⟩

private theorem block0:WideCovered band 7602109 9110848:=PRB band Z1.f2153 7602109 9110848 (WB 206367843448 17 0x185f0c40e7415725fc8b0540c2f861ffd80ab162a453e18e17c30fbb58554fdd227cc8b0be187b6702a8c53912d42785f0c3c3ca1539abc88e104c2f861d4760a9d1d6442bfae17c30e12a854da3d21f3b9b0be186a67c2a6ae290e8baf85f0c30bc4153c96c86bcc8b6d8772c0f7322be1c319dcdb6c348ee396f39baa14866edb6193901060b08a5081efd6db0c7386e241388a82fd60b6c862d1d50e4ece940f5a1596410a89b03831ee6036492cae084c56818e1912fd69d00b50c0045800211b07c90ac) (by decide+kernel)

private theorem block1:WideCovered band 9110849 9672240:=PRB band Z1.f1182 9110849 9672240 (WB 206367741976 16 0xcb1872248ae1643939630cb1871f5eaddb3e930d21c71871c452d9f53928412c718718f1ad623b91fb03c71871557ad239b9171f4c7187164a2ce2ff90e8e5c7087182b2caacd905fd6c708715742c7b6e8fd6c7c708712dfac59468f4db8c70870fc5ac2b5d8ec4a9c70870c5aabfc168e3b9ac308708912bcc568db28bc308704512b9be18d297cc3086ff762b6a5c8ca06dc308701b82b374d8c175ec308706e8ab054c8b8e4f) (by decide+kernel)

private theorem block2:WideCovered band 9672241 10338892:=PRB band Z1.f2154 9672241 10338892 (WB 206367743032 16 0xdf38764129e2a0727709337ce1c7cae7a402e9cb02ee34863f2f601a9be6e78433ce1cf114634d3e9a8bf2cf38738fd98a9762680b8f3ce1cd63e61fb149979d4cf2873844985778263c3173ca1cd66460d51c9867b6cf28732d51812cb25f7a9f3ca1cbfd65fbfae975598cb2872cf617cca525b32272ca1ca89c5ebea696437acb28726d3978b37256e9b32ca1c99805d974095315dcb18727aa974540252a13b2c61c94285ca144941f3f) (by decide+kernel)

private theorem block3:WideCovered band 10338893 11461675:=PRB band Z1.f1182 10338893 11461675 (WB 206367743000 16 0xeb587e304a5afd8d77215f5ac3eec5d27777eb74837ad61f485690fb69597fdfceb0f8d65472f3aabadd1e7587bb81a2fe35554dd9f3ac3dc4fd12eb26a626579d61ebaf887550f50eeefc690f48b0429c00a76559e3487992b20c687d3299e71a43cbc1d01e79295047b8d21e45c87fcdd9485e01c690f100f3f2a2aa31ce2e34877d821f3ac9d105626fa43b89a0f72a4683e29b7d21d876a7a56e73fcd11be90ec5d73c9ddb9ed46a) (by decide+kernel)

private theorem block4:WideCovered band 11461676 12092580:=PRB band Z1.f1182 11461676 12092580 (WB 206367775768 9 0x3cd61cc6bc5d8e10b884a4f3487296756d7d0addd46fcd21c8b0958d6ecb662fdf34871a6f55a6daed5437fbd21c48935469a9b43ec1ef38709cf948f656ccb28fbce1c18d7509173b21a85ef486ff6a53b4d82c4219fad61be22a4d1940aff649) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7602109 12092580:=(_Q1 band 7602109 9110848 12092580 block0 (_Q1 band 9110849 9672240 12092580 block1 (_Q1 band 9672241 10338892 12092580 block2 (_Q1 band 10338893 11461675 12092580 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤58)
    (hT0:3992≤T) (hT1:T≤4205) (hnu:7602109≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤24266187225847908:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAO
namespace DDC
open AI AP AN
noncomputable section
def band:Band:=⟨9,59,3930,4176,21875831038933556⟩

private theorem block0:WideCovered band 7733180 9081380:=PRB band Z1.f2155 7733180 9081380 (WB 206367843448 19 0x617c4128bc8548d2b62a48930be2091e8c2a2793b140f1b85f1047ab2150fc25897cf6c2f8822fd20a81bbec4792fe17c410f98853e4556219f230be2082dfc2a01e4b0fba6385f103de50150056d87529ac2f881c6520a84286c364025b6c4c061b32f54bd218f5b6db6228d4d8af68e350a507f6db10b46ee2f8c972841311b6d884345211ed0c1417ef1db6441a80d072d180a07a2d6cb220ab8f02f9eda501a70f65910457381425cb27fbe59b2b8215a72060a139bf5495d96440e2d084416e69f1fb3c1b22000ff000738e2f6d34208b10008300039ab87a5473) (by decide+kernel)

private theorem block1:WideCovered band 9081381 9649043:=PRB band Z1.f1182 9081381 9649043 (WB 206367741976 16 0xcb1894d6ead550b933b93cb18949ccad17a092b0fcc718945e8acd8f5922665c71894228aca8ac919bcec71893d962c673b911137c7189421e2c233b9086a0c708941df2bfa568ffc09c70893e762bc98a8f7173c70893ac7ab98608ee6dcc70893736ab76b58e5c45c708932cc2b45448dd1aec30892dd8ab12e98d4717c308928c22af3748cbc80c3089229baabfca8c31e9c308928422a89e78ba752c30892a4caa6c8a8b1cbb) (by decide+kernel)

private theorem block2:WideCovered band 9649044 10287664:=PRB band Z1.f2156 9649044 10287664 (WB 206367742008 16 0xe3489302f3d951c4e7d1871a442d3f1f655066f940b3ce25bd12c47495359fa99e712d6d7618fc09a453dcf38967d2b07f504cdd53679c4b393181364a64c03f3ca259c82bf6985314af19e512c8765f401a981ae2cf28960da2f58de4bc825e7944aea957885625c16d32ca25681cbb549d2cf63b96512ac435d153c95f086cb28951fdae3e234ab2f7e5944aaa316ffa92536d632c6254ee0b7027128a18396312a0ee5b08ce93c62a) (by decide+kernel)

private theorem block3:WideCovered band 10287665 11422991:=PRB band Z1.f1182 10287665 11422991 (WB 206367775768 16 0xeb68916ded26ad06b9343fada24460b4867c1ad37e1eb6890b3591cb666b08acf9d6240f2845b990ab0d85e7588fce25120346a7e15f9d623f13f4371dea8e32ae7588f6221095a569f37f38d623c15141711ca6b8cee3588e988d01be52968e838d623a8e53f6ad8a48e72e3488e5600fb45ee8de5138d2237cfc3e0f86a26416e3488d8edcf62ad2853ba37d22345ba3d2e83a039badf488c5ff0f248ce7c92337d222d9b13ca5b69e0f5e) (by decide+kernel)

private theorem block4:WideCovered band 11422992 12273815:=PRB band Z1.f1182 11422992 12273815 (WB 206367775768 12 0xf76897fb8d90851eed225fdd625dc54616748ba3608f75896b71d7ac0f6e4836bcd6257b665bbf70b80bacf34895385564a83adbd9fbcd225340156ee66b5e150f368942d31526f02d3308bbda24e6a25294bdb3b6f4ef689306bd424f42ca871bbda24add64eab19b18c99ef68923f55344a6ac1ddafada2471694b7f55af623d) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7733180 12273815:=(_Q1 band 7733180 9081380 12273815 block0 (_Q1 band 9081381 9649043 12273815 block1 (_Q1 band 9649044 10287664 12273815 block2 (_Q1 band 10287665 11422991 12273815 block3 block4))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤59)
    (hT0:3930≤T) (hT1:T≤4176) (hnu:7733180≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤21875831038933556:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDC
namespace DBN
open AI AP AN
noncomputable section
def band:Band:=⟨9,60,3869,4147,22482227536500631⟩

private theorem block0:WideCovered band 7864251 9012120:=PRB band Z1.f2157 7864251 9012120 (WB 206367843480 19 0x31c22884f5c2a12ba8898398c708a1ceed0a95596223ddeb1c2285c7002a9e6d8886b5bc708a121000aa9615e1f7cf31c228491902a3641687531db6d8b5ca9f4f723f961b1bfadb62f6e5f1b778f14863adfb6d8ac761d2eb5f04e148a86db629a9a8461d6c03840a63b6d8a4ff0e1296c98e0bc896db628feecc3c4799381d9e7b2c8a347b50cbdcf0e0306a6cb2289be0827b31237fa96cb2c8a252ec08e49d4dfa44bacb2288b484227a0c37d78f0b2c8a21e9f08ff1d4df182cacae28561c81c210227b4874aeb8813fa805106605e8c0d816e280125000724107917f8) (by decide+kernel)

private theorem block1:WideCovered band 9012121 9586055:=PRB band Z1.f1188 9012121 9586055 (WB 206367741976 16 0xcb18b6fc9ac26e3924587cb18b6b2e2beccd91b969cb18b66b02bc1dc912d4ac718b61bbab976e90a12bc718b5b922b5a3f90150cc718b5949ab2f278f88edc718b60102aed578efccec718b5f032acb158e70afc708b5a73aaa9818de490c708b55442a87028d5871c708b4fb52a71268ccc52c708b488faa49618c4033c708b40c62a3a608bb414c708b365d2a166f8b27f5c708b29f4aa13b88a9bd6c708b19302a1f138a0fb7) (by decide+kernel)

private theorem block2:WideCovered band 9586056 10159990:=PRB band Z1.f1188 9586056 10159990 (WB 206367741976 16 0xd338b9d933037309b0776d338b99592fe6d09a7b58cf38b95682fa2f399ef39cf38b90cbaf4ff899631acf38b8c6eaf09f898d6fbcf38b8dfa2eb3af984adccf28b8d1cae76ed97bebdcf28b89a8ae3fc797329ecf28b8597adfb2e96a67fcf28b81c6adc36d961a60cb28b7d3cad7c9b958e41cb28b78e4ad4376950222cb28b7427ad0819947603cb28b778cacbd4c93e9e4cb18b7797ac8aee935dc5cb18b7396ac520892d1a6) (by decide+kernel)

private theorem block3:WideCovered band 10159991 11236119:=PRB band Z1.f1759 10159991 11236119 (WB 206367775800 16 0xeb68b25cb9129e2156e62fced163c7a21bed4aa96b679da2c589542536d54a14df3b458a41a82e026a82a5de758b105b9023be14e243fceb16130e9fdf43297e7878d62c07a43ef6865270d1f1ac57c8067c6ee4a3c965e358af20c0f60d55456251c6b15dd691eaf39a8663ab8d62bc2513d024b50405671ac570c3e7a49329f686ee758a1aaa902668d3ca061c6b1569db9e5804674dfcb4d22b498330bc8d4e0fda699c5684e060f3de9b9395) (by decide+kernel)

private theorem block4:WideCovered band 11236120 12383989:=PRB band Z1.f1188 11236120 12383989 (WB 206367775768 16 0xfb68bc1e3d978b52f3dbd7eda2ec80f62a04abbdeb7f768ba25517dbac6eb19e7dd62e5d395c6d38b9ae3bf768b8aa556783b2e257f7cde2df87f576391b77dbff378b725495465cad99607cde2dae5652fe87b54d43f378b616f94425f2d0d41bbde2d5cee4f1b66b31cc8ef78b4cdbd34c0e2c8122bbde2d21804b7f72b0ec4cef78b402452812c6bf503bada2ce16d48b377aebbd0eb68b2f6911cc66ab68e4bada2cb40a45d3feac8b54) (by decide+kernel)

private theorem block5:WideCovered band 12383990 12455050:=PRB band Z1.f1188 12383990 12455050 (WB 206367775768 1 0x3eda2f3e0568a83bbe0c8a) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7864251 12455050:=(_Q1 band 7864251 9012120 12455050 block0 (_Q1 band 9012121 9586055 12455050 block1 (_Q1 band 9586056 10159990 12455050 block2 (_Q1 band 10159991 11236119 12455050 block3 (_Q1 band 11236120 12383989 12455050 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤60)
    (hT0:3869≤T) (hT1:T≤4147) (hnu:7864251≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤22482227536500631:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBN
namespace DDS
open AI AP AN
noncomputable section
def band:Band:=⟨9,61,3810,4117,21629505182317249⟩

private theorem block0:WideCovered band 7995322 8883764:=PRB band Z1.f2158 7995322 8883764 (WB 206367843416 16 0xbef8c2b71d09b07bf878e34bef8c2b13109acd1f874760bef8c2aafd09a9cfb87008db6d8b64982488881e86b9b9b6d8b9cede5530fe2862c12b6d8cccf162aeaefc8510c4b6d8c73beb17c39cc83f576b6d8c586fb126194082da28b6c8c410c40dc3d6881bedbb2c8c361180bc641080a38db2c8c2d53e0a69c907f883fb2c8c2495609a094c7e6cf1b2c8c26112087b1dc7d51a3b2c8c2458108c80d57c3655aeb8c196ea0574de07b1b07aeb8c186930552fd07a8d60) (by decide+kernel)

private theorem block1:WideCovered band 8883765 9409576:=PRB band Z1.f2159 8883765 9409576 (WB 206367808600 16 0xcb18c5e54e55727647ca14638c62e13f2a84fd23c1a071c63167169533fa11cf1b58e318af494a939848deb33c718c56cd45473e846aec6638c62ab002a2d562333f971c6314b2915170d118847d8e318a4caca8229c8bb497c718c49c9a548642459378e58c6163b92b2da022a652b1c231322014ab0451417478e1188b35ca6212a897dfcb6e8733fe2f75056c4782adf7c62b62026f1232218abafbe315b6c9371a391037b77df18af0749b260087d507) (by decide+kernel)

private theorem block2:WideCovered band 9409577 9989783:=PRB band Z1.f541 9409577 9989783 (WB 206367741976 16 0xcf38daf522df626986e97cf38daa03adb31f97e0f0cf38dab7e2d6eb3975349cf28dacc9ad30d296c5a2cf28da8aeacfd8f9637fbcf28da3cc2cbc0195aa54cf28d9f20ac881d951cadcf28d9a17ac5412948f06cb28d949b2c1fba940160cb28d8e8eabeaf29373b9cb28d8d482bb55e92e612cb28d9484ab694492586bcb18d90422b430f91cac4cb18d8b6e2b1e5b913d1dcb18d861a2afaf990af76cb18d8021aad9239021cf) (by decide+kernel)

private theorem block3:WideCovered band 9989784 10751304:=PRB band Z1.f1689 9989784 10751304 (WB 206367774776 16 0xe768d172cdf0a4829035239d63430597b2e9ea2f1fae758cff299ee0dda875ab39d633ab4b7d42aca0bb5ee758cb79b1f45d267e80435d233b3dc624a949e84c2d748ceab9d86c9ca77dc6f5d233a1a06119329d6974d348ce5fed81f962736f3b4d2338cc35fc3869c4e27d348ce21717c8a5a6f02034d2338c805e8c029b32d9d338ce116578352a6a94cb4ce337bdd5d8e269a178bd338cdcbfd7439626627933ce3368925c701698fc3d) (by decide+kernel)

private theorem block4:WideCovered band 10751305 11911718:=PRB band Z1.f541 10751305 11911718 (WB 206367775768 16 0xf388d8ae01455b72d7089bce23611194f60e3b4a6d8f388d793c1360f96ce2e2bbde35bd214bec26b2703cef78d651c5296656c553bbbde358096489830b039a0ef78d57f0d1d7796bc794bbde353e03462ad5ae0305eb78d4563512e1d2b39edfade3507fb4387d8abcc69eb68d3cf890a7ad6aac46fada34d181418754a995cde768d2c49d02dcfaa1e9ff9da348ccd3ff3dca75f31e768d22ba8fb85d2990f8f9da347b933e63dea52896) (by decide+kernel)

private theorem block5:WideCovered band 11911719 12636285:=PRB band Z1.f541 11911719 12636285 (WB 206367808536 10 0x3fde34448bb70c50e0683effbc683f346ab49ebfb7e2fb78cfe0dcce2dc77d3929f6d19e71298ce6faf6051beda33b5f2b01e055e32fc7dbc672e895d7aefbb4aabf788cdd7aab4f7f5745ebbef119b0b255f785ae4503fde2334901aade8fdbfc60f9c4665c22536263b6dd74) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 7995322 12636285:=(_Q1 band 7995322 8883764 12636285 block0 (_Q1 band 8883765 9409576 12636285 block1 (_Q1 band 9409577 9989783 12636285 block2 (_Q1 band 9989784 10751304 12636285 block3 (_Q1 band 10751305 11911718 12636285 block4 block5)))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤61)
    (hT0:3810≤T) (hT1:T≤4117) (hnu:7995322≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤21629505182317249:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DDS
namespace DAI
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DAI
namespace DDK
open AI AP AN
noncomputable section














open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DDK
namespace DDA
open AI AP AN
noncomputable section
















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DDA
namespace DAJ
open AI AP AN
noncomputable section
def band:Band:=⟨9,65,3591,3991,23939258742771510⟩

private theorem block0:WideCovered band 8519606 9011407:=PRB band Z1.f2160 8519606 9011407 (WB 206367876216 16 0xc7194172ea84b7191226033f1c650590ce12e6e248936ecc71941509604bdb59223b4230c2548b636b97018b88a325c3095188852d2c20ae2165070c2544d724b37679b880f5ec30950f1c4acca23ce1f15eb0c2542fe86b40a253877b97c30950a3adad9f616e1cc6cf0c253cf930a94b03286e7d0c3094f1d5baa85de6a1b0b7adb634997f8ade8a29869decb6d8cbdc1b9c295ce218289adb633ed40a981e83085765fb6d8c5a7c10dfd6b02113b46db630f410224b8ae8832743) (by decide+kernel)

private theorem block1:WideCovered band 9011408 9314054:=PRB band Z1.f2161 9011408 9314054 (WB 1306953111640 16 0x62c65701b29ac2f28e1f0662c656f9189a931e8dd52362c656ef4a9a66e68d8b3f62c656e3e29a3f568d415c62c656d65c9a1daa8cf77862c656c60a9a03628cad9562c656b20299f26e8c63b162c65698aa99ee628c19ce62c65677ac99fc468bcfea62c6564afc9a24ca8b860762c6560bd69a75b68b3c2362c655dfcc9a70068af240e2c65558d89b55b68aa85de2ca5457529d370e8a5e7ae3c6540a6c9cea498a1496e3c65371829d1fcc89cab3) (by decide+kernel)

private theorem block2:WideCovered band 9314055 9843686:=PRB band Z1.f2162 9314055 9843686 (WB 1305879402584 16 0x699ca8406eaac3509633e6699ca819d2aa15bc95a01f699ca7f118a9b800950c58699ca7c138a96f18947891699ca78750a942c893e4cb699ca73ebca93f8c935104699ca6df72a979fc92bd3d699ca66fb6a96404922976699ca5c772aa8adc9195af699ca598fca9591b9101e8699ca56feea7fc1a906e21e79ca3a654ab25d98fda5a6594a74ca89bc2508f4694658ca737109b8a408efcb1658ca71e209b37a88eb2cd658ca7094c9af5f88e68ea) (by decide+kernel)

private theorem block3:WideCovered band 9843687 10448980:=PRB band Z1.f557 9843687 10448980 (WB 206367774744 16 0xdb5952e08972631cfb82a6daca9555cb828da7b72376d6549c755b8f7b3c918daeb2a46a72d84cd9db4ffd75951f785697a94e909cebaca9078cb3a6167235cb5d654854959504537f357ae92a3c552c74d69b65e4d74951accd62114cd690eeba4a8b962b0407a68f95b5d2544b4a579d6133551fa692a1cc1ab9a789916c8d34950974d5b468cc418169a4a84d62acddfe5fbcef4d254286f560d292eb6e9a692a15882ad5d996c7ad) (by decide+kernel)

private theorem block4:WideCovered band 10448981 11243427:=PRB band Z1.f2163 10448981 11243427 (WB 206367775800 16 0xef89581f9d0250b1571f47df12ae6f2a01c4b2a9a05bbe25583b94049a454a04477c4aa35ae80a358a818faf38949dd1d0c0c374de2d9bef2a8fd518f3a6a97277f7de551c643183dd529b0c6fb4aa31d26237bea4a251df69542f8cc32e4d481d17bed2a7f39983d8328deb137da54f087302a1951737eedb4a9c4065fb0f4a25336db69534b3cbe1825437ee1b6d2a6657979698284aea76da54d1402ed08e504bf16daca989ea5d1ceca0041b) (by decide+kernel)

private theorem block5:WideCovered band 11243428 12454015:=PRB band Z1.f557 11243428 12454015 (WB 206367808536 16 0xffb952fc12b3c2b77c10ffff72a4c0e55dc90ef383cbeee547185aa8aa65ddcb27ddca88c78526e4fba91d6fba950d64ea0de9972d491f752a0b4913a8e0ae10aefdea53f4662657115b8d96fbd4a7a9004ad66cb5f39ff7a94f2de092b9f1699823ef329d8e11204312ce9213ce65392f9a340bd593e7b79cca6ec47454481b15568f3994dde2c882ebf605bb5e7329aeccd0bdb32bc1937ce6534560a11890d6ef5ff7c4a6541e41878bacb731) (by decide+kernel)

private theorem block6:WideCovered band 12454016 13361225:=PRB band Z1.f557 12454016 13361225 (WB 240727580696 12 0x85dca8061b258bf1b2f812617529e48288e36f0cabb9685d4a7376721bd96f2650220f729b4c848014fbc86c7b83dca67a499e831f71d13b60f9298e7aa74bdafc61d6083e4a5ef569becaf713d74a079296b8126b5a94c3ce4481e4a576cb99cc75f0a9ada07729510c46369ebc17f297fdca5126d180c347015e6dff7293866a5d1382bf300d) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8519606 13361225:=(_Q1 band 8519606 9011407 13361225 block0 (_Q1 band 9011408 9314054 13361225 block1 (_Q1 band 9314055 9843686 13361225 block2 (_Q1 band 9843687 10448980 13361225 block3 (_Q1 band 10448981 11243427 13361225 block4 (_Q1 band 11243428 12454015 13361225 block5 block6))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤65)
    (hT0:3591≤T) (hT1:T≤3991) (hnu:8519606≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤23939258742771510:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DAJ
namespace CZC
open AI AP AN
noncomputable section
def band:Band:=⟨9,66,3497,3507,25879962036737552⟩

private theorem block0:WideCovered band 8650677 8975571:=PRB band Z1.f2164 8650677 8975571 (WB 206367712376 16 0xc7196bfac5c0ad51c47a69e38cb605eb1c3606e22a8af1c65a69054f3e64d10bf098e32d2aa8acc4ec6883a31c30970b816a512a2440a6ee38cb408035c4369a1f28db1c6599121bb5507b0f49c58612e0682d48cf8c877f8ec309650fac4410edc39a73e38cb8d43ea6b6cee1c3e4f0c25b9bbd87780950dd47f8612dcc0ac598bf286c4ecb6d8d35d46f8e228c34fcc5b6c67212a92bca421953c2db631c480a42dcb10b7f436db18ff5c5ebbe50852a52) (by decide+kernel)

private theorem block1:WideCovered band 8975572 9281354:=PRB band Z1.f2165 8975572 9281354 (WB 206367712408 16 0xcb2960730099ab0aa367d2b2ca58035c26b7e1a8d54a2cf3960b3e89c2e92a3427ef3ce58a79626fcb198cbf54cb29612b5097bcd6231d2b72ca5846182596d878c2a05cb2961049096d719e2f7d7b2ca583a8825c9bf78b94b6c71971a8d6eec274a2d283f1c65c6719bf97ee68aff67cb29662a2540ec5962ad3031c65c3be9bb468a48a6a18c71970b5c6f72d48e287dc71c65c0f85bb94c9289d4c9c7196faff6e4c524626288b1c65b9dbda686830893f7a) (by decide+kernel)

private theorem block2:WideCovered band 9281355 9606248:=PRB band Z1.f2166 9281355 9606248 (WB 206367610936 16 0xd749732e6ab9edc94a346794b5ecd367f6a47fc673ca5aed69b11952368e59652d7154d5e669169cbcb296b5e26a4fe488f926594b594d3481424351f32ca5abca9a1eb12113ab9652d5604ce6ba903f2dcb296a68266d5547fa436594b507d32ceaa3ea77b2ca5a6b2995db91ebe6f9652d2694cb00c8f148fcb29689c2648f44764f46594b3f053293c239fd032ca59b949923011c69339652cb214cc7a48de9f1) (by decide+kernel)

private theorem block3:WideCovered band 9606249 10217813:=PRB band Z1.f2167 9606249 10217813 (WB 206367578200 16 0xd7597ba35731974df4aaebacbd932b71b5a6d501b5d65ea2559b6f5357d71aeb2f3a4abe9be9a2969d7497b63559c414cca0d6ba4bd7a2aa8b1a63fb2f5d25e9dd542d1d30d2f9ae92f3d0a9962297d42dd749793f5492774b9f6f6ba4bc392a3202a5aa63f5d25ddcd5110d52c2883ae92ec56a8ac42957ef2d749746854b0654a74d1eba4b8d22a91a5a5151535d25b30156cbab277e0da692c3fca5c0089329b7) (by decide+kernel)

private theorem block4:WideCovered band 10217814 10829379:=PRB band Z1.f562 10217814 10829379 (WB 206367610904 16 0xdf797015b00ff3a53e43df796fe02fb35fa4a8f4df796fa72f5521a413a6df696fddaf0394a37e57df696fb1aeb94aa2e908df696f842e6eb2a253b9df696f562e29cba1be6adb696f272de81ea1291bdb696ef1ad9bf0a093ccdb696eb82d4e5b9ffe7ddb696e79acfefd9f692fdb596ed7acc0019ed3e0db596eab2c85059e3e91db596e7bac4a249da942db596e47ac0f3f9d13f3d7596e0fabd4329c7ea4) (by decide+kernel)

private theorem block5:WideCovered band 10829380 11861396:=PRB band Z1.f562 10829380 11861396 (WB 206367611928 16 0xf7a9779923a813da7eca7bd4bb695185582cf4bdbdea5db9e89cd7f6550b1ef52ec6d43ccbeb17dbbf3997573a1603158298ef9ccba499070a36bca1ffce65ce34820fa55bfbc3e732e464409cb5acd344f39973a8a02942d5d45379ccb955101d776a9f823de65b6758b122152a6d5c712e1de31c3e4a828cde37970d898bc3953c9bf71bcb8550c47cde9bf8bf8de5c1ea618b1f4cd1c3bef2e093306b37a5d392) (by decide+kernel)

private theorem block6:WideCovered band 11861397 13084527:=PRB band Z1.f562 11861397 13084527 (WB 240727383064 16 0x83ecba304e9e43d8f4edf07c973679bf776f19f3460f92e57635b08c62a919c1f25c7c4674cc8c4279681e4b896ac6ca1d85f9f103c9706e57e81bf07496a0792e0072e43fce053de40f25bdef59f3f6bf7d1f7fe4b772aae32ff7ca502ffb96e8d15196a2f49f8dff72dc2929151dddfea2beee5b66f4ffc19bad2a87ddcb697c9c5899735014fbb96cfdd30ab7ee1f5b5f752d937254289dba967bdea5b0da48e822b62832) (by decide+kernel)

private theorem block7:WideCovered band 13084528 13542460:=PRB band Z1.f562 13084528 13542460 (WB 240727384088 6 0x87dcbe390a24623cea43c87dcbd6ac9875f4cd7c8387dcbca9c905d42cc51e585e4bbe7e8839c9cb274885e4bb33480b1b7c9fcaa85e4bab8c7a930fc8d20d) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8650677 13542460:=(_Q1 band 8650677 8975571 13542460 block0 (_Q1 band 8975572 9281354 13542460 block1 (_Q1 band 9281355 9606248 13542460 block2 (_Q1 band 9606249 10217813 13542460 block3 (_Q1 band 10217814 10829379 13542460 block4 (_Q1 band 10829380 11861396 13542460 block5 (_Q1 band 11861397 13084527 13542460 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤66)
    (hT0:3497≤T) (hT1:T≤3507) (hnu:8650677≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤25879962036737552:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end CZC
namespace DBK
open AI AP AN
noncomputable section
def band:Band:=⟨9,66,3536,3958,27350167341865496⟩

private theorem block0:WideCovered band 8650677 8937348:=PRB band Z1.f2168 8650677 8937348 (WB 206367876216 16 0xc7196cb6b9aa32ff5a217e131c65b13b10ade81be883a31c7196be318ad93f91a2053771c65ad7102c32073e87ef8ac7196aa1eab60319da1f28db1c65a10f98de6e0fd87a4e2c719639b6aaca8e4921dfe3b1c6584cc2bd7fd0d4875a3bc30966ac9ce1f90d8e1cd39f1c65dd2591a786c4b870f93c3097308b9315f95ca1ba8ff0c25cbd596c75948a86c4ecb6d8d39e892b4dc7061a7e62db634b3756a66c0a88654f0b6d8c952e094bcdf0216fe86db632a184c5fb4df0852a52) (by decide+kernel)

private theorem block1:WideCovered band 8937349 9243131:=PRB band Z1.f2169 8937349 9243131 (WB 1306953245816 16 0x64ca5860102136fe678d09fbe5ca583feb213ec12e8cbf54e5ca583f8a213c69b58c74ad64ca5860d9c13298bc8c2a0564ca586354e12faa4b8bdf5e64ca585f9ca130168b8b94b664ca58583e2131cf2b8b4a0f62c65d2ed42c9a98998aff6762c65d6d780d6071428ab4c062c65d2fdb6cfc9c9a8a6a1862c65d23a80d1d0e328a1f7162c65d20fd2d64fbba89d4c962c65cb8e38cb21e29898a2262c65cc4d36d5068e9893f7a62c65bf313ab98b6d888f4d362c65bf8b1ac88558088aa2b) (by decide+kernel)

private theorem block2:WideCovered band 9243132 9548914:=PRB band Z1.f562 9243132 9548914 (WB 206367741976 16 0xcb297efa4271fb891b472cb297ef322709369169cbcb297ed19a6fda8911f24cb297eca7a6e73990d47ccb297ea2826dd0e9089d5cb297e9b0a6c6b8903f2dcb297e69326be7e8ff486cb297e60926a84e8fa9decb297e1ef26a2e18f5f37cb297dce1a69fd28f148fcb297db5ca68c1c8ec9e8cb297d398a68fe98e7f40cb297d0cfa67e868e3499cb297c359268f3c8de9f1cb297bc242686c98d9f4acb2979ddfa6bb288d54a2) (by decide+kernel)

private theorem block3:WideCovered band 9548915 10141368:=PRB band Z1.f2170 9548915 10141368 (WB 1305879402584 16 0x6bacb92302ae796c9abeb86bacb9289ead87989a29696ba4b90790ace3c099941a6ba4b8e2eeac474098fecb6ba4b8b9acabb36898697c6ba4b88a4cab2a3c97d42d6ba4b8529eaaaebc973ede6ba4b80f4caa456896a98f6ba4b7e30aa9f6349614416ba4b7a8e0aa0614957ef26ba4b74260aa9f1494e9a36ba4b6b8ecab59c49454546ba4b5afaead328893bf066ba4b566eaabd25e9329b7e9a4b55f06a9ab819294686794b7d0649cb17091ff19) (by decide+kernel)

private theorem block4:WideCovered band 10141369 10752934:=PRB band Z1.f562 10141369 10752934 (WB 206367774744 16 0xdf797511397e79c5209d36fb4ba75d0bdfd468df95f7da5d2c815e676545d211bed2e8ebeaee7b7a253b9df697439b1750b650df356db4b9fdd0b9793e84a46f6da5ced425c2101412799b6d2e75df2dc12a9ffe7ddb6973caa56b820cfb497edacb9c96eb4cf1e7b4f836d65cd5f459eedd3c7d23b6b2e6319acbb189da942db5972d4e563f50ce89f9ebacb94574b1077e71fa935d65c8f9758092b37d2abaeb2e46eaabdb969b5406) (by decide+kernel)

private theorem block5:WideCovered band 10752935 11708504:=PRB band Z1.f562 10752935 11708504 (WB 206367775768 16 0xf7a97e345d16659acaa163dea5f52b44479ffb17dbbf3997c49e50d9ed2c14c77ce65ec86f426307af287ff3997b23f506814eb7f787ce65ebb5941311dacd344f39979ec5103af66aea29bce65e2745410772aa7e08f79969cd8d147b86a54dab8e25d9b09324860a828cde3797636f0c7ef5e9e4dfb8de5d7e7b31a133a6fe2fe37975bb08c5185a99a3877de5d5e7830ea3ea5d392df79753614c235a294f90f7de5d3d26302f30a4a8f4) (by decide+kernel)

private theorem block6:WideCovered band 11708505 12931635:=PRB band Z1.f562 11708505 12931635 (WB 240727546904 16 0x83e4bc59ac6c8549c5523383e4bbd46f6864a9c4279681e4bb5375647104c2fcf881e4bae96b60a0bec1d25a81e4ba8f255d81cac0a7bc81e4ba35885ae57fbf7d1f7fe4b9d25f5801debe52817fdcb998365548a7bd27e37fdcb948ce5305e3bbfd457ddcb8f92650d065bad2a87ddcb8b1c04ef9ffb9a80a7ddcb890d24cf587b87d6d7dd4b8501b4b49bfb752cf7bd4b80d8749a6a7b628327bd4b7c792480836b4fd947bd4b7c29746c762b3d2f6) (by decide+kernel)

private theorem block7:WideCovered band 12931636 13542460:=PRB band Z1.f2171 12931636 13542460 (WB 240727581752 8 0x9584b7cce7a49003fcea43c87dcb8d8bc934311ccd7c8387dcb85989123d0b2cc51e585e4b7d9a31135a7acb274885e4b763b71041e54c9fcaa85ecb711d78f7c328c8d20d83ecb6b7e08ec6004c7a76f83ecb665b90e21920c67cd1) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8650677 13542460:=(_Q1 band 8650677 8937348 13542460 block0 (_Q1 band 8937349 9243131 13542460 block1 (_Q1 band 9243132 9548914 13542460 block2 (_Q1 band 9548915 10141368 13542460 block3 (_Q1 band 10141369 10752934 13542460 block4 (_Q1 band 10752935 11708504 13542460 block5 (_Q1 band 11708505 12931635 13542460 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤66)
    (hT0:3536≤T) (hT1:T≤3958) (hnu:8650677≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤27350167341865496:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DBK
namespace DCT
open AI AP AN
noncomputable section
def band:Band:=⟨9,67,3448,3923,27280708727050568⟩

private theorem block0:WideCovered band 8781748 8994130:=PRB band Z1.f2172 8781748 8994130 (WB 206367876216 16 0xc71991f515abc5242a24f54b1c66488974ba6ab7a88f1e6c719918715b096c42a2299ef1c663a37feaa389b6885b0fc7198e404c2c845d7a20d56b1c66356abeb62b126880fa4c7198cd303316fbbfa1fa7bb1c662ef4e2d9cc64d87c438c7198828773416aed21e7a0f1c660df0bcbf7a33b8778cdc30981bfe25f716aea1d4c5f0c262730618d02bf2872d61c309958e9db0379c061c1eb30c26560538c2d684186e1f6c30995115bb06602461af102db636ae9eeccc42b886968a) (by decide+kernel)

private theorem block1:WideCovered band 8994131 9303049:=PRB band Z1.f2173 8994131 9303049 (WB 1306953245848 16 0xe4ca6073284131bd2c46fa04f2e53035ed3099888a236a2779729817ffb04d637b11aba65cb94c0a833026e8b078d11c6e4ca6060352131330346632db265303a0c2094e565631ebbd932981c14584a99fab185f08c58ccb81bb57952b748be41862c6659cd42b9ad09a45cc56b26531f12d95b109fce2d350593298b6cdda6d7f2c51603acc994c4e2c1d6328df28ab66a62c6659d466c39f73045357fb16332eaa7467a4d346287e518b1995b825b1677c0113a852c58ccb04a259d4c5b08988bd) (by decide+kernel)

private theorem block2:WideCovered band 9303050 9631275:=PRB band Z1.f2174 9303050 9631275 (WB 1305879402552 16 0xe9a4c58648a8c31f25ec56cf3991da493394fa497d519e73234cfa661ca4909f4b3ca645b8e4ca29091c87d6794c8a246992dfd22fa24cf2991310931e2ba44c699965322378262dc748731db2ca64411a4c3fba909acf6594c87534984b1d209ec8cb2990cd2d303522400fe1965321268260b3747dc46b2ca641a204c06668f6d216594c81ac097f5f11e436ccb298ff7192fd7023b592d96531f50ba5fca847457032ca63cc854c175c8e3f74) (by decide+kernel)

private theorem block3:WideCovered band 9631276 10249112:=PRB band Z1.f2175 9631276 10249112 (WB 206367774808 16 0xdb5994d7155a8cc538c731aeb328f372b1b24a6f33075d665168455d6ef4d9af56bacca2e88aab5da9a9f13d759944d0954270d341079aeb3288dcaa4c29a65c5975d264fbd0544a494c6d476ba4c9cb0ca857269843b8d7499324094fae5d2f59c3ae932539ba9d9e0a5c582b5d264812953c2474b3f99eba4c89a10a75c7a95e85dd7499094b54ed89d2aa30dae931e931aa2910a52eabf5d2637e8e5499c0ca11ec6ba4c673f8a8b2f0938d02) (by decide+kernel)

private theorem block4:WideCovered band 10249113 10866949:=PRB band Z1.f562 10249113 10866949 (WB 206367774744 16 0xe3799832357ec4752e882efbccbf196bdeb4694e8bb7de65e4165e373d4946afbef32f2942ecbe4a40c80df79978ef57387351bad4efb4cba5d2b891aa8b7b4b7da65c3405bccf5448ff7bed32d86d2d995da1b125db699675896a5a8508d276db4cb1590b4352a820ddf6da6583aa597a173fd941b6d32c454ac6aa89f55cadb699605d161a40cf5f79edaccae02eafddda78a0736d6655d835774973b228bb6b32a5cd2b8e6e9cfa6f) (by decide+kernel)

private theorem block5:WideCovered band 10866950 11948164:=PRB band Z1.f1613 10866950 11948164 (WB 206367808568 16 0xfbb99257ca917000b65084f7a991c6988eb046b522d6f7a99141348b4cf4b3f529f7a99123ca89012ab2c77bf7a990ac0c873712b199cdf7a990133a84e94eb06c1ff3a98f7c82838238af3e72f3998ec47e82799cae10c4f3998e984880d090ace316f3998dc1aa813b7cabb568f7998a94ea84efecaa87bbf3998c77d07e3a5fa95a0de3898c94626265b6a82c60e3798c835a61bbbaa79589e3798c5fdc6104f0a6feb2e3798c3b2c604c6ea667dc) (by decide+kernel)

private theorem block6:WideCovered band 11948165 13183838:=PRB band Z1.f562 11948165 13183838 (WB 240727579672 16 0x85ecc8247e3dcd95e495af42f663dbaf9d663eb1ff6c20fb31d62f6e0eeb38da00707d98e1d086b99d8c5a25583ecc6c51eb3c2e2623a5440f6633d1098e21030d1bea07b318d650bfedd384329b03c98c16a75cc246c0eb9f81e4c5cf432cd27fdfdef8bff262ccf055be9e6fa410dff931597f8a8c4537ac52cffc98a905b51de9cbc34e87fdcc51dc427ef35dd839dbeee627972937b002e76635f773135db09751297157c0fbb989719e4a2532b77e32) (by decide+kernel)

private theorem block7:WideCovered band 13183839 13723695:=PRB band Z1.f2176 13183839 13723695 (WB 240727581784 7 0x4bda642150915fd6cb45a0be57b3330e3687f25cba07ae10fd995f92b299aab8cf0fc287ecca34de1365d8266f10ac3f664d3bb49222f8332d19e17d3242d2e44b32c1970d750be9910c6d2082280ca590c) (by decide+kernel)
theorem covered:WideCovered band (AX band) (tail band):=by
 have hh:WideCovered band 8781748 13723695:=(_Q1 band 8781748 8994130 13723695 block0 (_Q1 band 8994131 9303049 13723695 block1 (_Q1 band 9303050 9631275 13723695 block2 (_Q1 band 9631276 10249112 13723695 block3 (_Q1 band 10249113 10866949 13723695 block4 (_Q1 band 10866950 11948164 13723695 block5 (_Q1 band 11948165 13183838 13723695 block6 block7)))))))
 intro nu hlo hhi
 apply hh nu
 · exact hlo
 · exact hhi.trans (by decide+kernel)
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K
theorem AS {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T 9)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:9≤wt RCN156.BE F.val) (hB:wt RCN156.BC F.val≤67)
    (hT0:3448≤T) (hT1:T≤3923) (hnu:8781748≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤27280708727050568:=
  AI.AS K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end DCT
namespace DCU
open AI AP AN
noncomputable section


















open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K

end
end DCU

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AY
open AI AP AN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def band0:Band:=⟨7,61,4246,4626,8688366028624013⟩

private theorem _AA:WideCovered band0 7995324 8897818:=PRB band0 Z1.f443 7995324 8897818 (WB 206367742104 16 0xbef897a53279db4f87c51abef897277a7a032e874288bef896912a7a2d1d86bff6bef89521aa7cba5c863d65c2f89372127edd3b85bad4c2f88eac9287692a853842bee895483a6f605984b5b0bee893f9627138d884331eb6d897acea4c10f783b08cb6d89799024a2cd6832dfab6d8975baa49444582ab68aeb82e7fc14c21048228d7aeb82d47693118c38123b4aeb82f98b1743342801e90aeb82d9771419ab17e1449aea82ca8d13633607c0a02) (by decide+kernel)

private theorem _AB:WideCovered band0 8897819 9432629:=PRB band0 Z1.f444 8897819 9432629 (WB 206367742104 16 0xc7089b328a967bcf8fee35c3089aef6a93cc6e8f6ba3c3089aac029188dd8ee911c3089a7b8a8ef91c8e6680c3089a970a8cad6b8de3efc3089abbb289ba8a8d615dc3089a85f2880c498cdecbc2f89a4cc28677c88c5c39c2f89a0c1284ade78bd9a7c2f899c83a8339568b5715c2f89974a28109d58ad483c2f8991fa27fb6d48a51f2bef898be8a7e84a389cf61bef89849327d0f12894ccfbef897f3527c300188ca3dbef897f44a7a3fa08847ab) (by decide+kernel)

private theorem _AC:WideCovered band0 9432630 10335124:=PRB band0 Z1.f445 9432630 10335124 (WB 206367774872 16 0xdb3890bdf599a14fced9ca6d9c483376cb74afa72b9c35ce2401a36544afb375299ae711eeffb23286c9aa429d7388f1c4d910945cccf836b9c474220c8a696a62678b5ce23572d64ab0f32f297fb67110ad833a01c8968f9bd7388d2d418b5243cac53ce78c47243ab595fda5215573c62388a35a89ecb2700638e311c24e2a2f2c4927b0ec7188e07354ff489c8fc3ee38446f728a769b4a45d7af1c2237511536d0a321e6b38e111b6f3298f1809070c7) (by decide+kernel)

private theorem _AD:WideCovered band0 10335125 11404747:=PRB band0 Z1.f446 10335125 11404747 (WB 206367774872 16 0xe76895444df031b7d702e5f3b44a772ef4c7c7ab4029f9da252278788ad3b57f707c6d128510bb68cbcaaf660e35893c4b9d46b1dd4f89ef1ac49d20ee6e562aa3b0678d624d52c7221db34fcdedbeb125e96b841188a6e1d2df58929ea1bcd033d2ee586fa4494910dbaa7da935e337d22490a16c96feb47a4d1be9123e6ab5ba2a4a2cd44db48919c01a90b09d0e4116da448a340d294b0a830bfb6d22457b26839fe33f7bb5b6712224133a6ef09eb8b7) (by decide+kernel)

private theorem _AE:WideCovered band0 11404748 12273815:=PRB band0 Z1.f447 11404748 12273815 (WB 206367775896 13 0x3cde26e40a4fbb07cbb4897f3789af78d3763a2ee90dd3cde2699e84c4981ab93e50f37899c0552a4baa6e0e4b7bde264add49146c8b73409ef7898bdb51e3995ed8bb9fbde260d3d462e426b529c3ef7897b81113ce156d0927fade25cadc438f4c4b31f7beb7896dcc1096e54ec86967ade259bf7414dd92b11535eb6895fb8100bb7c6c040479da2561693f10760af0aed) (by decide+kernel)
theorem covered0:WideCovered band0 (AX band0) (tail band0):=(_Q1 band0 7995324 8897818 12273815 _AA (_Q1 band0 8897819 9432629 12273815 _AB (_Q1 band0 9432630 10335124 12273815 _AC (_Q1 band0 10335125 11404747 12273815 _AD _AE))))
def band1:Band:=⟨7,62,4182,4598,8903611066907167⟩

private theorem b1_0:WideCovered band1 8126395 9039471:=PRB band1 Z1.f448 8126395 9039471 (WB 1305879369880 16 0x61845da3f53cc5afc4f737b0c22eb3be9e30cfa25a95585f1747dc4f07f1b11cc76c308b99c02796b2c88622161845bc1e93e8e95c3ef0470c22bea2aa28bd2a1d67bd85f16b9094ed9c330dabaac2f8b5c68a72ae588651bb5d6c5d148925e873c2e6d0aeb62e763a929369a15262175b172fc5491a0ab098adcb2c83266a97c2dc4844154575c183be4aab8c1c19c90acb20d1b066b84e8a08c3b96570622052dea20300410eaeb82f3019588b107e1021) (by decide+kernel)

private theorem b1_1:WideCovered band1 9039472 9580552:=PRB band1 Z1.f449 9039472 9580552 (WB 206367742104 16 0xc718be0dba9806ef923008c718be07da95061e91abeec718be342291f01d9127d5c718be136a90160c90a3bbc708bdd5fa8e118b901fa2c708bd918a8bd3ba8f9b88c708bd47e28995898f176ec708bd008a8815188e9355c708bcacb2862ee78e0f3bc308bc4bd283fd168d8b21c308bbf18281c7e58d0707c308bbdb1a808f648c82eec308bbd6427ed7338bfed5c308bbe74a7cb3928b7abbc308bbfe427a8ba18af6a1c308bbac027a2ef08a7287) (by decide+kernel)

private theorem b1_2:WideCovered band1 9580553 10493628:=PRB band1 Z1.f450 9580553 10493628 (WB 206367774872 16 0xdb48b2adb99e0b6fd00f5e6da4591bbecd2833a7c5a276d22c7a4f65e98bb3c1cabb6916423eb289aac9d0622db48b1c84193190dcdfef7ed9c58a658c8fdc6a6bd6ef6d22c2dec64ce57333db13be9154a16341747898e555db38adb4c98fb513cbee91e994581a22b60f81a5b53bf4ca2bf51f5ad3fcb2b997996315f620aa54db494c488cb18af92a1515879ca2037e58c57b8b4a7f5e4a4ef1571c62bd397539eb632670798e315e5a1a9ab4b092b422) (by decide+kernel)

private theorem b1_3:WideCovered band1 10493629 11575792:=PRB band1 Z1.f451 10493629 11575792 (WB 206367774872 16 0xeb78b81415f9d2dfd850f875bc5bce7cf8e2e7abe66f79de2dcae97a9841b5d2313ced16d5f73c4b1dcad8956e768b68449db63bdd64091f3b45b0e2aea6126aade3bf8da2d6e3d73b013354e17bc6d16a9443903c38a96889e358b5265dc2146bd4302bf1ac5a6a2ade4f81a9d608f8d62d1ef76df7d2b4c9fe1beb1682de3651414a547bcdf58b3b295addb41d21fc4efac59dd2ed45540a8cdd5b7d22cdaa3694b503445e45be9166199b426400a126ef) (by decide+kernel)

private theorem b1_4:WideCovered band1 11575793 12455050:=PRB band1 Z1.f452 11575793 12455050 (WB 206367775896 13 0x3de22fe4b6523de0cbe0c8af788bee3c940bfeaef4115fde22f88d44e687cabbfc23f388bd636d3294ce6ebcfc7ce22f290b4ae6bc8b9ebbdf388bc2849255d89ee38e2fce22ee25c47e8276b7db57ef88baeaad19f22d6db4c93be22e927b4510114b5caf0ef88b9eec10f3654ed30af7bde2e59424297a12b3ba8aeb78b8e1b105daf06cac95bade2e151940416a0b1aa23) (by decide+kernel)
theorem covered1:WideCovered band1 (AX band1) (tail band1):=(_Q1 band1 8126395 9039471 12455050 b1_0 (_Q1 band1 9039472 9580552 12455050 b1_1 (_Q1 band1 9580553 10493628 12455050 b1_2 (_Q1 band1 10493629 11575792 12455050 b1_3 b1_4))))
def band2:Band:=⟨7,63,4120,4570,9138472916805888⟩

private theorem b2_0:WideCovered band2 8257466 9181123:=PRB band2 Z1.f453 8257466 9181123 (WB 1305879369880 16 0x63846ea54d3d4ff7460be1b1c23728089e864362e48858e11b7a764f50ef9161900c708dac87a7a1a9b8a86de63846cdeb13db35d45009eb1c235f30a9fcda2625ee718e31ac257500ddd111ebf4c308d91ef271e8f7887058e1846a73593c849343f55baeba36fb80928a3d61d945575d1b7e3149060490dbee6b2c8574a99b788f38659d259642a2588c13999c2a747adb216a61e807588a110d316590a8d1d32c6b6304598ab2c852b9817052b080163f) (by decide+kernel)

private theorem b2_1:WideCovered band2 9181124 9728475:=PRB band2 Z1.f454 9181124 9728475 (WB 206367774872 16 0xcb28d0d7b94c77d7ca38ede594685c56a5b7afa4fb0e72c63424fd5286dbb26cd319631a0df4a91f13c92e0f6cb18d04a8147f835c92daae58c680ef2a34fe2a4756d31c633fc1a515f71322a0258e319f80ba89092890ca70c718cfbbd9439143c82267e38c67e59ea1143da3efcb71c633f57b504094b1e73178e319f742280a8448eb3eac708cf8ca13f6541c71724e38467aeb49f5e54a36a29f1c233ca9b4f946631a460b8e119de0327c07c08c9d64) (by decide+kernel)

private theorem b2_2:WideCovered band2 9728476 10652133:=PRB band2 Z1.f455 9728476 10652133 (WB 206367774872 16 0xdf58d48a11a1df3fd144f2efac6a4804ce9227a85fa877d63517b866a9a5b40e6bdbe91a7e1db304e9c9f681bdf48d3796d96f015cf2e6c6fa4696d26caf70ea7546577d2347ce9654e653388ca5be91a1625334e9f89b3b0fdf48cd988599869bcd17e6eb9c68d8d6b73601a6492275ca344a625b2ff4b30328d9e51a2636aa79cd4970e03cb28d10c49525bf9cb4431659468732ea882c8a580b032ca34301153d50e32afa3d9651a19e429ba28094f77d) (by decide+kernel)

private theorem b2_3:WideCovered band2 10652134 11746838:=PRB band2 Z1.f456 10652134 11746838 (WB 206367775896 16 0xef88dae4e501afb7eccf85bae23694ab3f4967eb232d2eb78d9d118f954336c49e3fade3660cf3d35b6cb01c4ceb78d90a4cf13c36ebc4427ade3625d23b7d89aae05c6e778d8212ceab61a6b3ea0f9da35f13f39c7828abef40e768d77fece3ddb9eab8ffb9da35c7d8385c436a9d8bae368d6a860de5d956a335df8da358bbd36dcda4a7c233e368d63368d8fb5ce9adbc78d635765035c2362a5abaee358d570e0d4d58c69281ab7d6353e57349c4a0a39527) (by decide+kernel)

private theorem b2_4:WideCovered band2 11746839 12636285:=PRB band2 Z1.f457 11746839 12636285 (WB 206367808664 13 0x7dcc68f61e551be9cc0d07dfb98d18574a5d3bb77f8a75f731a21379434082afae7dfde63426f1277cf54ded75a7bcc681b3a4cf72d8bca371f798cfda529693baf77305fef319efa412704adaea33afce633c7042414f5adcc0d479cc676e1546aa2c4b87664f388ce87088a8ca676ed645df119c6ea9100084ad97f7fbe2337991215c2f8daaa4df7c466dc354184bc0b44958) (by decide+kernel)
theorem covered2:WideCovered band2 (AX band2) (tail band2):=(_Q1 band2 8257466 9181123 12636285 b2_0 (_Q1 band2 9181124 9728475 12636285 b2_1 (_Q1 band2 9728476 10652133 12636285 b2_2 (_Q1 band2 10652134 11746838 12636285 b2_3 b2_4))))
def band3:Band:=⟨7,64,4060,4541,9385324670065082⟩

private theorem b3_0:WideCovered band3 8388537 9322776:=PRB band3 Z1.f458 8388537 9322776 (WB 1305879402648 16 0x638c77e3869ef3dba3904618e31df23ba7b520d8db9ee638c77acc49ea9a7234cb118e31de0eaa7a836b8cab9b658c77176c9f75bea3091c99631da2eba814f798b9d496594759428a1ec9222c587f8e31d4ae1a8530178a8ef5638c76b6789c0c59a281f317df1df1d0a48ee458980a25f7c77bd8091eb8d223e5e56db0de138a08732388724f5b6c3681e27153b4e1d8ff56db0e281c26c5a428655aa5b6436a81c76e02c610e40d6d90d61391971220821c5e) (by decide+kernel)

private theorem b3_1:WideCovered band3 9322777 9876398:=PRB band3 Z1.f459 9322777 9876398 (WB 206367774872 16 0xcf28f23c814de90fcb59d767947909caa64897a58b2133ca3c7b3b52e39db2b4ab79651e37d3a946a8c951e31cb28f18cad48d885ca4b84e59478bcfea3bb42a503f7f2ca3c5ff2518dfb327116b9651e31cd28990f893018ccb28f17149440f03c93d31658c78a31ea18a69a47cce72c63c45dd5087e4b22d81f9631e1cc7282b16490e4e6cb18f0ad3d407309c82edee58c78366a9fcabca3f5a4f2c63c0a6b4fd1c631e9ed58e31dfc9a27d1a508ec840) (by decide+kernel)

private theorem b3_2:WideCovered band3 9876399 10810637:=PRB band3 Z1.f460 9876399 10810637 (WB 206367774872 16 0xe368f6fc4da52fdfd27a86f1ac7b4d38d0e15ba8f9aeb8d63d874c678ba5b45b0cfc6b1eb411338808ca1ca14e358f4fce99a0605d05de0efac7a0f3ccbe0fea7eb5bb7d63cc07f66441d33d3e39c6b1e24d4b38a2489d90c9e358ed6691a2579bce413beb9c798052b7ef2da6dd08f5ce3cb7155b7592b34cba19e71e53952aa521499577dcf38f278f553c631cc682a679c794376a90b6ca6124af3ce3ca1b5541e6632f84039e51e4c3829e45f0973ad8) (by decide+kernel)

private theorem b3_3:WideCovered band3 10810638 11917883:=PRB band3 Z1.f461 10810638 11917883 (WB 206367775896 16 0xf398fdb58506deffed768efbe23f467f40a02eeb4cbe8ef88fc7590fd963b6cef657be23f08fd3e5bdecb2af42ef88fb9fecf5df56ec683bfae23ec27b3c73feab0929ceb78fa74a4ededc66be112bade3e94793aaf5a8ae75f7eb78f9d0d0e769d1eb59e979de3e54103911756ac5951e778f8d344e17a096ad2bfb9de3e2e6b378b5d4aa3cabe768f84b04dbb100ea4b9679da3df8023665172a82006e368f76378d72ecc69c46cb8da3db70f3523b30a6035f) (by decide+kernel)

private theorem b3_4:WideCovered band3 11917884 12817520:=PRB band3 Z1.f462 11917884 12817520 (WB 206367808664 13 0x7fd47a1d3458212ccc39470ffa8f3a6f8ab9cdf7850c3bf751e62db14e31bab05df2beea3ca333a8b3db4e034bc7dd47913254f59968bf5b25fba8f1b56e9b3af8f7c99a7ef51e27ce12f27c9af4f9ffdea3c329d2503bcade18167bcc78431d48871f4bb21d9f798f021e68e073e774270fe731df81651647f4ae414d3ce63bd92ba21e2e0dbfb7079cc77967842e8630b6e88d) (by decide+kernel)
theorem covered3:WideCovered band3 (AX band3) (tail band3):=(_Q1 band3 8388537 9322776 12817520 b3_0 (_Q1 band3 9322777 9876398 12817520 b3_1 (_Q1 band3 9876399 10810637 12817520 b3_2 (_Q1 band3 10810638 11917883 12817520 b3_3 b3_4))))
def band4:Band:=⟨7,65,4001,4511,9654687671835447⟩

private theorem b4_0:WideCovered band4 8519608 9464428:=PRB band4 Z1.f463 8519608 9464428 (WB 1305879402648 16 0x659488bca29f2457641a9b1965222d5ea7a96fc8fe1ba6594889b469e7ba2e3d64259652218c0a7ab6ea8ed05865948827ba9eb9326391e9d96521db8fa7fec188dbef5e594856e28a3a0cde34d91196521ca49a78c2668cad92658c872d929cd591630938596521a153a7785548b9c30617c88369e921718e2c4df975d0e95e3a9aebe28a8acd5b6c387cd2894fd8a25e5a975b0efe143126ad18868085b6c3884de8ed2b461915096db11a3be1cc835084227d) (by decide+kernel)

private theorem b4_1:WideCovered band4 9464429 10024321:=PRB band4 Z1.f464 9464429 10024321 (WB 206367774872 16 0xd3391394994f835fcc7ac0e79c89b0b0a6f837a61b3433ce44cb8053244db2fc83d9e722660d295e0fc975b6dcf3913347949af3dcb695e679c899778a43182a59282b3ca44c08b51ca7d32b82b39e5225af428c96a89538a8cf2912a7c9455213ca57fb679489380ca21065a509d173ca448da850cc4eb273d27965223e50a8406449315e2cb2911ce114150f9c94698e59488dedea03e98a4812032ca446dee4fd6dc322f79d9652232dfa7dc73090f31d) (by decide+kernel)

private theorem b4_2:WideCovered band4 10024322 10969141:=PRB band4 Z1.f465 10024322 10969141 (WB 206367774872 16 0xe76918f339aa762fd3b01af3b48c364ed3309fa993b4b8da45f544689cafb4a7ae1c6d22e58233e99cca42c0de36916b1ad9dbf3dd18d5571b48b46b8cd89a6a8825238da456e3d66f371341efcbc6d22844cb3be7b89fe682e7690cededad5fc3cf6a9071ac892f8ccb0f9da770ef76d24539865bf654b3964b5a692289242acd7749ba0f8d349143d8554fab9cd8c23e99c8a0b38a9d0fca6a3e574ce44faac5485f63340dc9a672278362a1b8f0997e32) (by decide+kernel)

private theorem b4_3:WideCovered band4 10969142 12088928:=PRB band4 Z1.f466 10969142 12088928 (WB 206367808664 16 0xf399104cec86485df70ecc1e7321fe03507af37add93f7ce643ee692053816db29cd79cc87b6df3fad18cb54238ef990f1b827d408776861abdf121d8838f61abeacc7dcbbe243a7c51e3c1ccd9070877c4872ee03bb1238b0fcadef890e15aa75afb4f5fd697d7121b8f14e7c661abb67a3ae2436be51c842a2d6e442f5bc86bc07386dbd4acb722eb790d37a26f86a07574b81cef219e02cdc33e8aaa51779de432a451b2a958d4c17d73bc8657a235b44c0a87198) (by decide+kernel)

private theorem b4_4:WideCovered band4 12088929 12998755:=PRB band4 Z1.f467 12088929 12998755 (WB 240727547032 13 0x81dc8b4da15b9bd7cc6586381dc8af9ec5928adbc547007fdc8aa40d56a693ac4359d7fdc8a4dbb5423ab9c3243b7fdc8a129351efaf8c212d87fdc89ccc54fed3b7c101767ddc898ba14e13e96bff0137ddc89571d4c17005bedeb07dd4891bd64a68034bdcd4d7bd488e2b948ce683bcbbeb7bd488ad054755242bbaa887bd48886e345c3d71ba99257bd488578f4478a60b987c2) (by decide+kernel)
theorem covered4:WideCovered band4 (AX band4) (tail band4):=(_Q1 band4 8519608 9464428 12998755 b4_0 (_Q1 band4 9464429 10024321 12998755 b4_1 (_Q1 band4 10024322 10969141 12998755 b4_2 (_Q1 band4 10969142 12088928 12998755 b4_3 b4_4))))
def band5:Band:=⟨7,66,3944,4481,9960853498960835⟩

private theorem b5_0:WideCovered band5 8650679 9606080:=PRB band5 Z1.f468 8650679 9606080 (WB 1305879436440 16 0x679494ab6927db5bc9293c067949495fa27cbc9b9209876794947d1e27c477a917f4e679494605a27d0b4990f51467949439f727d6a78906adc679494150b27db7f78fe0a2679c93d51628197568f5669679493d4df27be0058ecc30659493f1f02735cb48e41f6e59493622a27b6f538db7bd6184945a0224872428d2d835d7447919b3945fb18ca34a5d7445a91c2b026618b8ed85d7448ded444a85a18a7a655d7445a0322cbcdf08851805d6c447253230a07086289b) (by decide+kernel)

private theorem b5_1:WideCovered band5 9606081 10172244:=PRB band5 Z1.f469 9606081 10172244 (WB 206367774872 16 0xd34934d88d50e8cfcd9baa69a49a6f6ea7a48fa6ab46f4d24d3a36536821b3445c3a6926994c2988d4c9998a8d339349bfd4b096dcc8737e99c9a3560a4e6c6a6210db4ce4d0d885224b532ff3fba67267fea28ef188976fc3cf3933c5f546890bcb72c5679c99c890a2aaf5a596d433ce4ce43a50fc76b2ba22f9e7267036a8646749546decf39337f2d41f2b9ca5e52e79c99ba0ea06b18a50c9b33ce4cce585006e232750659e5265efc27ee240931df9) (by decide+kernel)

private theorem b5_2:WideCovered band5 10172245 11127646:=PRB band5 Z1.f470 10172245 11127646 (WB 206367774872 16 0xeb793ad109afa1e7d4e5af73bc9d1c62d5d563aa2dbaf9de4e608e69d681b4f44f1cef273159b4654aca68e06e779395edda13ff5d2bcca73bc9c635acf98eaa9194879da4e011467828f346a15fced26e1ebb3e6878a23c3ce77931ec69a9cbcbd093e573b4998312cce755a804d637d64d8d885c9a02b3dfdcbae926b9a4ab0ad249dea72d74935a1a156eda1ceb01d6ba49aba34aac3b8a7358035d24d508e54fd70338978fa6926a1742a48e609bc18d) (by decide+kernel)

private theorem b5_3:WideCovered band5 11127647 12259974:=PRB band5 Z1.f471 11127647 12259974 (WB 206367808664 16 0xf7a931ca7e8973d7f76250def5262ec110d4cdfae7f84fdea4c48d5a10a64edc74d07bd49865444101f4cb7d52ef3a93068747fa64776d8179e732605444fa810aad6b127ce64bf9101ed584cda4bebf9cc97c7cc3cb08d8b38364ef992f3840776c4af64dde5df325dfb6ceb8539ac56a03be24bb5911d0352ad82306f7c497459a393e2d4af319aeb892e3fec7108a275c3a51d7125bd7a0def1b4ab422d7ae24b7c7c9b89858d5fa21f5bc96d8a136878a0aadfd0) (by decide+kernel)

private theorem b5_4:WideCovered band5 12259975 13179990:=PRB band5 Z1.f472 12259975 13179990 (WB 240727547032 13 0x83e49c9ccf5fc472cc91c5683e49c30f65cc95fbc807e481e49bcadb59fc2eac6f37181e49b78fc573d149c5deff81e49b22aa54e1fd8c4ca8c7fe49ad4bb52c9697c3b61a7fdc9a8174508be36c2a1a87fdc9a47c84e7d345c18d357fdc9a04694cb2ef4c078c27ddc99bfac4ae2413bf64507ddc997cff4917992be4fdd7ddc99583e47acda1bd3b6b7dd4991ed446315c0bc26f8) (by decide+kernel)
theorem covered5:WideCovered band5 (AX band5) (tail band5):=(_Q1 band5 8650679 9606080 13179990 b5_0 (_Q1 band5 9606081 10172244 13179990 b5_1 (_Q1 band5 10172245 11127646 13179990 b5_2 (_Q1 band5 11127647 12259974 13179990 b5_3 b5_4))))
def band6:Band:=⟨7,67,3888,4450,10286840860176571⟩

private theorem b6_0:WideCovered band6 8781750 9747733:=PRB band6 Z1.f473 8781750 9747733 (WB 1305879436440 16 0x699ca4dd53280903994bd15699ca4cd3d27fe6b9943154699ca4bf8e27ec70893a592679ca4adf927dfbc79319d1699ca48ea927ed607928e11699ca468e927f9b9692024f699ca41cce283c93691768e699ca3cdab285d80590eacde79ca39574283f4c4905f0b679ca3b84327a0e638fd34a638ca4b6e3247cf528f47895f7c5ca6cd59b66618ebbc85f7c58a67d3d865d18da4465f7c5f5a0c70dd5918c8cc35f7458777d3dea5218a5dbe5d74556fe228f7010882eba) (by decide+kernel)

private theorem b6_1:WideCovered band6 9747734 10320167:=PRB band6 Z1.f474 9747734 10320167 (WB 206367774872 16 0xd759569ba95206b44ebc93ebacab3542a84859e73b59b5d2558ea253d38af38c349ae92ac14529c5f469bd5e3d74955ce614c96db4da511e9a4aacb9ea5bf2d66af9874d25554e5527bbcb346541a692aa85d29191d499a6dfd3495544794745e9cc8d8ee9a4aaa13ca3030ce623d734d2554a59512dba5300737a672a9e69a87c5029777dad33954b7ed431458cb760ce99caa397aa10f0465981634ce550b485068e012ba92fa672a7a452811bd09548d5) (by decide+kernel)

private theorem b6_2:WideCovered band6 10320168 11286150:=PRB band6 Z1.f475 10320168 11286150 (WB 206367774872 16 0xeb895caa99b5682f561b4375c4ae016cd83c676ac7c13ae25707386ae6219540f03d712b7395b50459ba8efffeb795af55da53bb553ec3ef5bcad25fed251f669b03ebade5655bc68df7314b52f3d6f2afe8ab461ad7a491f6eb7955f17da9a34351bd3a73bcaab3a8ce93d56898bcb7d655d9a75d302894296dfb6b2ae5552b4eb13a033eddb5956f89558fd894fd4166bacab5f0cab966067c71af5d655a3ed5563ac33d2155aeb2ad2d0aa75e209e04e8) (by decide+kernel)

private theorem b6_3:WideCovered band6 11286151 12431019:=PRB band6 Z1.f476 11286151 12431019 (WB 206367808664 16 0xfbb9534f168cc797f7b5d57f772a61845142bc7af25ca7eee54a56521cf8c6ddbfd37bdca91547426352cba6824f7a951bdc08252d5772a145ef52a314ccffe146ae0e47fdea544aba9f735f4db90cf79d4a864a73dd6a08b60a1bf3a9506524798c1ef69e533e732a08e60ef3899acf6c5fce653fce11d7943ad961ca77cca7d3683a3dda4b1ac11ef994f44a67297b07612921df329e7bece20f10abdf437be253be609bf8ce8d732c5f7c4a7555b374dad0ad4e08) (by decide+kernel)

private theorem b6_4:WideCovered band6 12431020 13361225:=PRB band6 Z1.f477 12431020 13361225 (WB 240727547032 13 0x85ecae008a6438f6ccbe04983ecad7fd860dc5abcac8c783ecad03515d9fd7ac9b14483ecaca9b75ac76e9c899c383ecac494a584dbd8c7824081ecabe0a2559c557c66abe81e4ab8c4c5345256c5533c81e4ab473a5132d45c43bb981e4aaf63a4f286b4c324367fe4aaa61a4d288d3c20cb57fe4aa6ee84b3f792c0f5327fe4aa2c0e4998f61bfddb07ddca9e97947f9170bec62d) (by decide+kernel)
theorem covered6:WideCovered band6 (AX band6) (tail band6):=(_Q1 band6 8781750 9747733 13361225 b6_0 (_Q1 band6 9747734 10320167 13361225 b6_1 (_Q1 band6 10320168 11286150 13361225 b6_2 (_Q1 band6 11286151 12431019 13361225 b6_3 b6_4))))
def band7:Band:=⟨7,68,3834,4419,17709205970077753⟩

private theorem b7_0:WideCovered band7 8912821 9889385:=PRB band7 Z1.f478 8912821 9889385 (WB 1305879503992 16 0x69a4b150118281b3e92dccd2d349629b0005009192596481a692c528e909fc8624ae5ebb4d258a2e5a13f2ff4953e8e69a4b13f40827e49a929628cd34962690104fedf32508ff1a692c47ef60a0d57649cb59f4d25874f58147edfc93096a69a4b119f1827ae80724f842d3396233f904e9932a47bb5da692c40c6a09e710d48b0c730c2350258a86e83e090d4455f7c63f23c46aa69311f7368c2f8dac9f42dec11e63a7c857df18c0ef315145804634fe2fba30f65721ac36688a34d8) (by decide+kernel)

private theorem b7_1:WideCovered band7 9889386 10468090:=PRB band7 Z1.f479 9889386 10468090 (WB 206367774744 16 0xdb5977e0915436ecfdd7d6dacbbd464a95dfa7cb6c76d65ddb7c54500d3d40cfaeb2ee5eca9f8539e131ed75976f4314e4274ec2eb6bacbb78cca65f3e73e2375d65dbc7452cd5d38d689aeb2edd252937b19bddfad74976b25148a0ccda858eba4bb3bd0a3c4e66b0da35d25d8e10519e49346c3fae92ebe62a8adea99a8d6d74975a6a5446d54c8dc6e9a4baad12a1ba6a6239134d25d500c50a1e13001f7a692ea4602834fc9773b2) (by decide+kernel)

private theorem b7_2:WideCovered band7 10468091 11444655:=PRB band7 Z1.f480 10468091 11444655 (WB 206367774808 16 0xef997e9511badcff5d435fdf32fd37f36af73eb61c73be25f7f536c64ebd6364577c4beabf8d74740ab51f8ef897c8ff5ab7751546ecdd712f73c4b51fe42a47353ae25ea79469e06854012175c4bcc962d3ea4ca6e7b0ef8977189dac55814b9a3ddf12e365eb6ab31a92ca338da5e55085db66cd1cbfcedb4bc3d1aae6350a27d67db697846ed5aeb3943e03fb6d2f0940ab21172858b5b6da5e123055cb40506ac66dacbc0ae0aad8e8a04843) (by decide+kernel)

private theorem b7_3:WideCovered band7 11444656 12602065:=PRB band7 Z1.f481 11444656 12602065 (WB 206367808536 16 0xffc97511e090aee18095a3ff92e933291b6c26fcc0fbff25d064222b42d5f0ad67ddcb9cbbc43f950bcfb1afbb9734fda85277d77c111f772e5c741059a22eb17dbdee5c9d7c201e335cd5b27bdcb902d63f1387b890d2f7a971d8227be5d76eec81ef52e2f5acf40a06d96ebbdea5c46b61e0a2b5aa08df9d4b85b5c3b26dab42689f3a97098007470c76617f1e732e09a30e5e732c7c597ce65bfdbe1c6147586b69f7ccb7cd79380dfcafbc40) (by decide+kernel)

private theorem b7_4:WideCovered band7 12602066 13542460:=PRB band7 Z1.f481 12602066 13542460 (WB 240727546904 13 0x87f4bf84cb694f1acea43c85f4beed6c658dc7cd89aa85f4be5ebf61fc15cc6f1885f4bdf73b5eedc4cb548685ecbd7ff95c01e4ca39f483ecbd0ac4592702c91f6283ecbcb350567a0ec804d083ecbc53055426f1c6ea3d81ecbbf48551e39dc5cfab81ecbb973d4fad0ac4b51a81ecbb5bbc4db4afc39a8781e4bb0e514be3c0c27ff57fe4bac1524a1acfc16562) (by decide+kernel)
theorem covered7:WideCovered band7 (AX band7) (tail band7):=(_Q1 band7 8912821 9889385 13542460 b7_0 (_Q1 band7 9889386 10468090 13542460 b7_1 (_Q1 band7 10468091 11444655 13542460 b7_2 (_Q1 band7 11444656 12602065 13542460 b7_3 b7_4))))
def band8:Band:=⟨7,69,3782,4387,18249700045487415⟩

private theorem b8_0:WideCovered band8 9043892 9811672:=PRB band8 Z1.f482 9043892 9811672 (WB 206367876216 16 0xd7598230108518470e56db635d26095ac81405116952807d749825aab04f24cd65264db5d2608bb3813eadcd940a65cf29828ecd0495b8b24dee533ce60a25a012dce4b92ecc3cf3982857b84b631ae4a956f3ce60a03ea12d5563925df3cf39827bb304b4b2ee485a2f3ce609d5a012d15eb91cf21cf39826db204b4602e461ee70c22f35caab90e3da914050c308d17b461c16baa242c5fefbe31e208e30958e08f93ddc2f8d91cf3a9230ce639d8eefbe319ef882b64ae08c3af7) (by decide+kernel)

private theorem b8_1:WideCovered band8 9811673 10396648:=PRB band8 Z1.f483 9811673 10396648 (WB 206367774744 16 0xdb699832bd4d059cf51f46daccbfa06a5dcb678545f6d665ee0f52b52f3b0c8bb6b32edfea9325b9cf774db599720f54853f4e3451ebaccb67eaa3afa26f674b5d665ad845198b9369605aeb32d41728a6ec9abc31d759968a9144112cd16b06baccb2cf8a1d07e667a3b5d6658ea350a735321f7daeb32c2be28350b9880edd75995b9314129fcbf90e6baccaa89aa0bc965d8d2f5d665323f505d152da8f7aeb327db7a844c09645aa) (by decide+kernel)

private theorem b8_2:WideCovered band8 10396649 11091305:=PRB band8 Z1.f484 10396649 11091305 (WB 206367774776 16 0xef999bc7e9ac849aa4f5a7ce666074c6d3530a81fc8f39990f449bfcb869c089b7de668c7d58bf6ea5e484df7999ed4d60edda9556cb7de66771257b570a4c6e1df7999db615d114290e0477de666e3456d084a3a940df69997eb55995fa8c69bf7da66508455fa06a28b9edf699909455693c287f33b6da6631965538eaa16dfcdb69987f39532efa837caf6da661c23545cf8a0505adb699868615020e27f062b6da661ad95396509f32b9) (by decide+kernel)

private theorem b8_3:WideCovered band8 11091306 12261257:=PRB band8 Z1.f485 11091306 12261257 (WB 206367808568 16 0xfbb993583a80a435bb1789fbb993108e7e9737b9f9e8fbb9929f487c5f55b8dc45f7b99236f27a7c9db7bea3f7b991e0147844a5b6a101f7a991b23c76a041b5835ff7a9914dba74df99b465bdf3a990f05273767bb3481bf3a9907e7e71ba77b22a79f3a9908044705e6bb10cd7f3999031586f06cbafef35f3998fdb166e2221aed193f3998f6c326cf4dfadb3f1ef998f015e6c7b2aac964fef998eaeaa6b88ceab78adef998e50406b6deaaa5b0c) (by decide+kernel)

private theorem b8_4:WideCovered band8 12261258 13431207:=PRB band8 Z1.f486 12261258 13431207 (WB 240727546904 16 0x85f4cec559601e7dccf1a785f4ce34d35cbc16cbd40685f4cdd7bb59fefccab66485f4cd61a757414dc998c283f4ccf71b54d215c87b1f83f4cca0ce52423cc75d7e83eccc4926504731c63fdc81eccbeaf34e262bc5223a81eccb95434c41f8c4049881eccb59df4a5562c2e6f781eccb12df48ca00c1c9557fe4cac4f44717d3c0abb27fe4ca80eb4597d6bf8e107fe4ca5614441d3fbe706f7fe4ca1a9b42e3c3bd52cc7de4c9dd5741a795bc352b) (by decide+kernel)

private theorem b8_5:WideCovered band8 13431208 13723695:=PRB band8 Z1.f486 13431208 13723695 (WB 240727579672 4 0x89fcc896d137a2eee8b417c3fe641e779ac05eb412a361ff31fcd28cdd9559e59d70ff98f4f98635b40ce0f4a) (by decide+kernel)
theorem covered8:WideCovered band8 (AX band8) (tail band8):=(_Q1 band8 9043892 9811672 13723695 b8_0 (_Q1 band8 9811673 10396648 13723695 b8_1 (_Q1 band8 10396649 11091305 13723695 b8_2 (_Q1 band8 11091306 12261257 13723695 b8_3 (_Q1 band8 12261258 13431207 13723695 b8_4 b8_5)))))
def band9:Band:=⟨7,70,3731,4354,19655013439877081⟩

private theorem b9_0:WideCovered band9 9174963 9803161:=PRB band9 Z1.f487 9174963 9803161 (WB 1305879503992 16 0xebacd10763c2893ddb2b2b32d749a272f884e72f12541501ae9344a19709d907e4a3a73b3ca68aa8c6122f56b93e48e679cd14ebdc255d56526a86acf39a298af04ab360a4c30259e734526480955fc94961ee33ce68a332412abe9a927bb0679cd143ea8254dda5246708cf39a27ee284aa84aa47ad619e7344e76c0957e5948d195b3ce689956812b91ba915aff61846fe575587377a32225a4c308cedbe796e4db264209e57df18e0c4115ba4e0c7b0e430be2e9c478a6576888e4116) (by decide+kernel)

private theorem b9_1:WideCovered band9 9803162 10394407:=PRB band9 Z1.f483 9803162 10394407 (WB 1305879402520 16 0x6db4dc76e8a49c527a6c9db6b371556a8fc0c9e0ace6dacdc3532a3777e75e9d5b6b370396a8b3d49cea1c6dacdbe816a2614671670db6b36eec92876519bc96a6bacdba3baa15e426ce449aeb36e3cea841299aa8b96bacdb7f82a0772a686181aeb36d89528101b9988076bacdb4d409fbe9a63debdaeb36c79fa7ef179867566bacdaf83a9f659e5f5bf5aeb36a616a7f7de9746a46bacda2eb4a01f225ad92faeb363a9828a3cd9625f2) (by decide+kernel)

private theorem b9_2:WideCovered band9 10394408 11096512:=PRB band9 Z1.f488 10394408 11096512 (WB 206367774776 16 0xf399bb4591adf2a2a54703ce66dbeb16dbb3aa8310eef99b8fd6da56c169c41737de6ec00557b3c0a5efaadf79babe515d0c2a957d477de6ea55a56b9a2a4cef8df79ba918d591aca90fa837de6e9ffe55c354a3ae47df69ba488d55a6928c77bb7da6e81fe54faf6a28d95df69b9cb4152894a87f4f77da6e60f7543282a16ce4db69b93f914f697283722f6da6e4692536858a04c32db69b90f894c3ff27eef676da6e43fb5299f69f2b80) (by decide+kernel)

private theorem b9_3:WideCovered band9 11096513 12279004:=PRB band9 Z1.f485 11096513 12279004 (WB 206367808568 16 0xfbc9b3fdce802e7bbb5cdcfbb9b3c7a07dc621ba3c2afbb9b359287bbc73b91b78f7b9b2e79c79b8adb7fac6f7b9b2714077b78bb6da14f7b9b2572475be45b5b963f7a9b1f630742d25b498b1f7a9b1907c72a4c9b37800f3a9b1239a7123c3b2574ef3a9b0e3766fa809b1369cf3a9b0cc626e5015b015eaf399b073b86d7010aef538f399b00ba46c8a7aadd486f399af92d66bc8a0acb3d5ef99aefdca6b3adeab9323ef99ae74dc6b04e0aa7272) (by decide+kernel)

private theorem b9_4:WideCovered band9 12279005 13461496:=PRB band9 Z1.f486 12279005 13461496 (WB 240727546904 16 0x87fcdf790260653bcd67f885fcdee62e5d1b19cc474685fcde75605a00f2cb269485f4ddfdee575a19ca05e283f4dd8bf254d8bfc8e53083f4dd1df95274eec7c47f83f4dcd43750437ec6a3cd83f4dc75e84e3a90c5831c81ecdc188f4c3cf0c4626a81ecdbcffe4a4797c341b881ecdb89e3489f05c2210681ecdb3cad470582c100547fecdaef1b45714cbfdfa27fe4dac35743eac8bebef17fe4da82ca42a0adbd9e3f7de4da418a415ad6bc7d8e) (by decide+kernel)

private theorem b9_5:WideCovered band9 13461497 13904930:=PRB band9 Z1.f486 13461497 13904930 (WB 240761134104 6 0x89026cf4f11ec25cf50b08a2409b2f3f17542edd30b7089026c887e1c1cc5f47aafa1bf9b15af26be828d0ca0d86fe6c274859e602b3ea56e1bf9b0110c63d282ce88aa) (by decide+kernel)
theorem covered9:WideCovered band9 (AX band9) (tail band9):=(_Q1 band9 9174963 9803161 13904930 b9_0 (_Q1 band9 9803162 10394407 13904930 b9_1 (_Q1 band9 10394408 11096512 13904930 b9_2 (_Q1 band9 11096513 12279004 13904930 b9_3 (_Q1 band9 12279005 13461496 13904930 b9_4 b9_5)))))
def band10:Band:=⟨7,71,3681,4321,13746442873853440⟩

private theorem _DT:WideCovered band10 9306034 9735498:=PRB band10 Z1.f489 9306034 9735498 (WB 1306953245816 16 0x68d270a99e212be794948d4a68d270a689e12c62fc94445a68d270a3e8812c754493fb6a68d2709eb9212d860493b27968d270999b412e3d3493698968d2709222412f8bbc932098e9d2708164c1339b2c92d7a8e9d2707756a134a403928eb768d27096f9c12ad6229245c768d2709c45e126b58991fcd768d27098fcc12717a191b3e768d27093a301284e89916af668d2708df8e129545191220660c2359f64a850810890d91560c2331e5ac49ead209047345ebe319cd8026619008f2372) (by decide+kernel)

private theorem _DU:WideCovered band10 9735499 10276998:=PRB band10 Z1.f490 9735499 10276998 (WB 1305879402584 16 0x6db4ec30b6a1a9c09cd0866db4ec19e2a145849c3ea56db4ebfda4a0f2f49bacc46db4ebd892a0ba749b1ae46db4eba22ca058149a89036db4eb6024a067b099f7226db4eb0a20a0af389965416db4ea07daa2656498d360edb4e7dbbea5ff0c98417f6db4e9f1faa0271b97af9e6dace9de7a9e9426971dbd699ceb1962925c05968bdd699ceafb1691f9c195f9fc69a4eae6a2961f8495681b69a4eac9d6962d8c951f2b69a4eab3bc960ce494d63a) (by decide+kernel)

private theorem _EL:WideCovered band10 10276999 10874515:=PRB band10 Z1.f491 10276999 10874515 (WB 206367774744 16 0xe379dba4d559b7dd2f749f1bcedb198ac10269572cb8de76c6d25598e14995a3bef3b59b8aa9204a438f1df79da928152f5cd1d3886fbced43c2a8ad3e8c54bf7de769fad53ef3345069dbef3b4d0529ba4ca1f16ddf69da28014ca0a50afc66fb4ecf1e8a5bb768336af7da7666ad52956b407795bed3b28572919a59fa9eadf69d8eb8547b934f8c04edb4ec5e6aa358967a18a36da7626e9516dd13be88fb6d3b0f6ca8948f9d6267) (by decide+kernel)

private theorem _FG:WideCovered band10 10874516 11920168:=PRB band10 Z1.f492 10874516 11920168 (WB 206367807576 16 0xf7b9d2842ae96f0ab5e328f7b9d21d64e5b71ab4bf66f7b9d21352e2e4feb39ba4f7a9d1a798e02a4ab277e3f7a9d147badea33cb15422f7a9d0c3fcdc3e78b03060f3a9d03b70db1084af0c9ff3a9cff344d9429cade8ddf3a9cf66e4d98a0cacc51cf3a9cea0d8d9ccb8aba15af7a9cb36fce1c924aa7d99f3a9cd526cd4ad9da959d7e389ce12eeb0b204a83616e389ce0fb2afb02ca7a435e389ce104aae76aca71254e389cdf1eaada8c8a68074) (by decide+kernel)

private theorem _GB:WideCovered band10 11920169 13115202:=PRB band10 Z1.f493 11920169 13115202 (WB 240727546904 16 0x83fced5e5750bcb0c81f4283f4ecf6b44e9e08c6fb8083f4ecad044c7666c5d7be83f4ec579c4abdf6c4b3fc81f4ebfa5948dcecc3903b81ecebad3d47347bc26c7981eceb74f74594fdc148b881eceb2e84443db0c024f67feceae0e742c4a2bf01357feceab3b9416de5bddd737fe4ea816840564dbcb9b17fe4ea3e9f3f2173bb95ef7de4ea01283e1b71ba722e7de4e9da663ce79cb94e6c7ddce9b4173c0e9fb82aab7ddce979093b1d25b706e9) (by decide+kernel)

private theorem _GW:WideCovered band10 13115203 14086165:=PRB band10 Z1.f494 13115203 14086165 (WB 240761135160 13 0x98f674771a9bf5e49d6f0158b027546b18fafaecd5cc548b027503f74ef2a18d4a892890274c97cce4e2aad384d18902749543cda70d6d2610f89027467844d2711ad13d4e870274385e8ca388ed0198c8702740e5f4c2faf2cef5cb870273ed038bbf7eecdd20986fe73cb32cb63218ccae4884fe73aa314b09a92cb8a8684fe738efc8aabf8cca66c584fe7374328a64376c94303) (by decide+kernel)
theorem covered10:WideCovered band10 (AX band10) (tail band10):=(_Q1 band10 9306034 9735498 14086165 _DT (_Q1 band10 9735499 10276998 14086165 _DU (_Q1 band10 10276999 10874515 14086165 _EL (_Q1 band10 10874516 11920168 14086165 _FG (_Q1 band10 11920169 13115202 14086165 _GB _GW)))))
def band11:Band:=⟨7,72,3581,4287,15988617535880926⟩

private theorem _KL:WideCovered band11 9437105 9871076:=PRB band11 Z1.f495 9437105 9871076 (WB 1306953244824 16 0x6ad678bc0a4252d869969ee46ad678b9fcc25345789655306ad678b7c2e253a4f8960b7c6ad678b53062543ab895c1c76ad678af7922566e489578136ad678a2aac25c01e7952e5febd67883e7426a2b3694e4ab6ad678ad45a2502b45949af66ad678a843a251fd85945142e8d278ac5b0249c9b494078ee9d278a67ae24bdbf493bddae9d2789e57024f1944937425e9d27893aca2534e53932a7160c22be8716a25f8b292e0bc60c2351884ed40c4a1924d5360c233e274ea22fe30912681) (by decide+kernel)

private theorem _KM:WideCovered band11 9871077 10418259:=PRB band11 Z1.f496 9871077 10418259 (WB 1305879402648 16 0x6fbcfdbb2ea071fe67be14dbed3f61d8a80ba099e64ea6fb4fd4bec9ff3d22774605bed3f418b27f0d089d3e196fb4fcc2349f89dde72aac1bed3f1f1127f37c69c17476fb4fc285ca013ada6e0f79bed3eefb4281d0359af0756fbcfb3c78a0cdb52697435bed3eb2b8a817ab399c9a4edb4fab5d29e5848a64d8eda693f1f69a4397e198a2d369a4fc6b249074bc6603da9aeb3f09f1a52f430977c016bacfc041c94b16025cc935aeb3ef749a52b71096e898) (by decide+kernel)

private theorem _LH:WideCovered band11 10418260 11022046:=PRB band11 Z1.f497 10418260 11022046 (WB 206367774872 16 0xe789fef8a5582b0454176f71c4ff5042ab1a65e9e6dd78e27f975a5517ccf4e1019c713fc991aa52f76a674a4e389fe3ea550c032d2f09df1c4ff0ee4a78271695374b8de7f73e4535df094974d5c6f3fb0052982124a42701e379fd316d4aed51d1c9cc71bcfe6b78a4c8c8e8c00bf7de7f1fea520326544d98dbef3f8c38a8d6d42a1d95edf79fc3d6945b640d0a2faefbcfe0e88a237b4682ca337de7f00cb50bba81403e47bef3f7b07a8381209f8bbc) (by decide+kernel)

private theorem _ME:WideCovered band11 11022047 12078673:=PRB band11 Z1.f498 11022047 12078673 (WB 206367807640 16 0xfbc9f4f5dceab177ae13947ef27d3a8539aea7db7277ffbb9f47d7ae464e32d802b7eee7cfe2338616cbb4d9dbf7b9f364fadebd3eacecc2fdee7cbbf53743419b28c39f7b9f2ccf4daa66a2c595a3dee7c9e1eb678997b03e96f7b9f21976d88679abc5f1bdee7c47f036778c5adf0f4f7b9ee1634df73c12b3288fdea7b9e06b5a6bb3aba351e799f0088aafc018aa9f2039e67bfb982bac631a9e918e789efc8f0adc9006a556bf9e27be92fab3f530a8c247) (by decide+kernel)

private theorem _MZ:WideCovered band11 12078674 13286247:=PRB band11 Z1.f499 12078674 13286247 (WB 240727547032 16 0x85fcff75e752892dfcabb6785fcff0d3d5034c2ec9949685fcfea23a4e0734dc86dc485fcfe38bb4c2673cc746f283f4fdc5b24a1a26bc6202183f4fd8874485d68ac4f94f83f4fd293546b2a79c3d27f81f4fcc999450e228c2abad81f4fc7222439fe97c184dc81ecfc4ac142417b6c05e0a81ecfbfa8c40f0ea5bf37397fecfbb1513fd25d4be10677fecfb69a63e86e83bce9967fe4fb45173d5be52bbc2c47fe4fb07633c80221ba9bf37de4fabec63b7c950b97522) (by decide+kernel)

private theorem _OC:WideCovered band11 13286248 14267400:=PRB band11 Z1.f500 13286248 14267400 (WB 240761169048 13 0x135fcf9aaead021387cd9b4088d067b2b4fe428dbf5ec469bc6833d7fa311f8d32eb5d99962c19eb64080f080d53ac7f29160cf570be8727aef8d518c28b067a9ac8636f4e9be9f8f944833d3df7d1a49685b4b2c822419e98caa0ca146eba3489f1204f499f68614ee84d07d7d87027a379ea2f0a6b1e7ab5643813d109d416acc54b38bf6e1c09e84af38afc80c39a12150e04f401164552c170cbe238) (by decide+kernel)
theorem covered11:WideCovered band11 (AX band11) (tail band11):=(_Q1 band11 9437105 9871076 14267400 _KL (_Q1 band11 9871077 10418259 14267400 _KM (_Q1 band11 10418260 11022046 14267400 _LH (_Q1 band11 11022047 12078673 14267400 _ME (_Q1 band11 12078674 13286247 14267400 _MZ _OC)))))
def band12:Band:=⟨7,73,3535,4252,21628528594209425⟩

private theorem _TS:WideCovered band12 9568176 10006654:=PRB band12 Z1.f501 9568176 10006654 (WB 1306953245848 16 0x6cda80c233612b15dd4c583f366d405fe53095a57aa619819b36a02f42504ae613330371cd9b501748c025764e997d1156cda80b68b212c39644bc34f366d4058b75096a06225cf095b36a02ade484b9928f2de35bd7ad014e5c025c90f696a734ebd680a146212ea94acb2e5e75eb40503d1096491d2584911ab5a02cbfa8492f8c72b8f98d5ad014d9bc24f1fb3957d53ebd68090c3e12cc4694a996db06111d8a682559718653a189830889a82d0c3a932328a6e4c1846dc26ed17f6cf0932990) (by decide+kernel)

private theorem _TT:WideCovered band12 10006655 10559519:=PRB band12 Z1.f502 10006655 10559519 (WB 1305879402648 16 0x71bd0dfdb0a1c45fa84807dc6f43738ca84cf6da08b2e71bd0da79ca0fbd727fd8f9c6f435e2628379db9f614e6fbd0d4c20a07e62a7b3175c6f434076a82ad399e376c71bd0c99aca124d627689edc6f4308a6285c9e79d0d8befbd0b2d82a32e79a71e26bbef42bfba2853b759be3a96fbd0bfe089ceee926d3ae1aeb4341e4244bcf39ab9c86bad0ce92090d328a689361b6d431e4aa563031998fe76db50c60e0957d3426515bdb6d43109da56220098faf6) (by decide+kernel)

private theorem _UQ:WideCovered band12 10559520 11169577:=PRB band12 Z1.f503 10559520 11169577 (WB 206367774872 16 0xe79a1ff70d5acb5fd53794f3cd0ff224ac7393aa768e39e687f59e55b4dfb528a8fcf343f4fd2aa4d3ca8b058e78a1f53695354c5d40db3f3c50f81dea8f14aa9e19db9e287abe7541d7534de30bcf143c982a9d42a8a65c94e38a1e0a9d4d3983d2e3d271c50ef6e6a5eb65a94cacf8e2877686527db8b493b85c7143b7dd2912af4a408d2e38a1d9525475589d1b9f0f1bd0e9af4a30100a8b7bc78de873635514a503449401c6f438dc12886960a1b510) (by decide+kernel)

private theorem _VO:WideCovered band12 11169578 12237177:=PRB band12 Z1.f504 11169578 12237177 (WB 206367807640 16 0xffda16582aef2f57eeae5e7ff28575f7bada39eb98f98ffca155c40e8dcd76e196dbef28530bd396af7cb73bd4fbca145d58e29156ed847d3ef2850d65b8233fab4e812fbca13df58de60ea6cef8cbeee84d1e03735dd8b29450fbba129f5edc8e91ec5a9c3eee846bc23724fd6b0408efbba10552edf40456bc5ab7eee83e3feb63e3e4adeccceb9a10a254b18168eb30bafae6841d982c196a2ac2dfaeb9a104d34af76e46ae642b9e68408942ba2140ab041a) (by decide+kernel)

private theorem _WP:WideCovered band12 12237178 13457293:=PRB band12 Z1.f505 12237178 13457293 (WB 240761134232 16 0x87028423189580e6bf355e361c0a101b77534be9ecc2dab870283e563943a24f72c0f2a140a0f18ec4ebb15cc9d9e884fe83ac22131cc46f22c01e13fa0e59024ab86dac7862684fe837b399237fea71971160bfa0d806f470eb48c5326482fa83533f915ff01f10220e0bea0cf3584407b16c2dea180fa8327ac10ad1c9706d30203ea0c420541453c4c08ade80fa8307784ffa490efd83fa03da0bda143ef19f2be371c7ef682e2d90f746a86f434edfbda0b38de3cb3570bbe35a) (by decide+kernel)

private theorem _XU:WideCovered band12 13457294 14448635:=PRB band12 Z1.f506 13457294 14448635 (WB 240761169048 13 0x13a050e005e56c0f20cdc77fb8f0a83887bc482c1d5eda70d468541aa9fb2221e1eb6890e2342a0c8946101853b3b1f4b11a1505fe78c7ab3b48d7d0768d0a82d8f163a745d3eb534b4585415a73b1bdec49b55f2d22c2a0a66b60d5655cba8a5a7160d04fd71066afc14d328f289068264126315e1f1e8ff88c483412673317c1f44b4354c2241a08e59e8b78c9839f569f0e050448c3858b5630ce816d) (by decide+kernel)
theorem covered12:WideCovered band12 (AX band12) (tail band12):=(_Q1 band12 9568176 10006654 14448635 _TS (_Q1 band12 10006655 10559519 14448635 _TT (_Q1 band12 10559520 11169577 14448635 _UQ (_Q1 band12 11169578 12237177 14448635 _VO (_Q1 band12 12237178 13457293 14448635 _WP _XU)))))
def band13:Band:=⟨7,74,3489,4138,19540459979123170⟩

private theorem _ADB:WideCovered band13 9699247 10142232:=PRB band13 Z1.f507 9699247 10142232 (WB 1306953278616 16 0x6cda88597b609603b726b0861b36a2160bb4258970b9a76dc6cda8856d650963652e68ae81b36a21558782590c9a99e0646cda8853111096a83266654a3b36a213f6fc25d42889949ebedda884c7b3097d6f9e63fabfb76a21156c02666bc798b372edda88419ab099b6a9a61a0d9b36a21244a425a4db5981cfa6cda8851ef1092f8c525f46fdb36a21412c024c7eb39786826cda884dc58093a728a5ced198308631db2c446e14196f00962c62c1c0c45a6b5a825966418318a4cf47c6a1ed10952c9f) (by decide+kernel)

private theorem _ADC:WideCovered band13 10142233 10700780:=PRB band13 Z1.f508 10142233 10700780 (WB 1305879402648 16 0x71c51ced90a28f27e8d1fb1c714733a0a892f9ea2b17371c51cae94a1eddb6886be9c71472397a85e99ca1848371c51c66eca11972e83b829c714709eba8440daa0579171c51bdb68a1070267f0465c7146c9a828917989f2aa0f1c519ef9ea46811e7a509fc714641c9291f2f69dfdae71bd1ad8289e34116759cd9c6f468c0aa7c90a49cd0be6dad1baf92914d3ce70e915b6d46e066a588e529ba3cd6db51b67449620ac66d6245b6d46d47ea57cb909b0d54) (by decide+kernel)

private theorem _AEB:WideCovered band13 10700781 11317108:=PRB band13 Z1.f509 10700781 11317108 (WB 206367774872 16 0xebaa3ddde15da707d657ba75d51ed612adcba3ab063efae68f59e856857fb570507d7347a35e2b0bbccaaec0beb9a3cc72156805dd52ac973cd1e373eaa501aaa6fc6b9e68f09ce54b9db3525143cf3478327aa1ff08a89228e79a3c0a494f407bd3fdd7f3cd1dfc50a6e831a9d94df9e68eebdc53171cb4d9d7dcf1476bd9a9646a4a63846e78a3b044149c7f1d2d0e773c51d52c0a45174a942d579e28e8e3751d5cc348e9b9c71473f8ba8d45f0a3de65) (by decide+kernel)

private theorem _AEY:WideCovered band13 11317109 12395682:=PRB band13 Z1.f510 11317109 12395682 (WB 240727546008 16 0x81ed1a71f47a27edf7a494503da345c0af08f5faefdec1ffb4679661d9c94edd655fbff68cd9273a7809cb99dcd7fed19ac3a7339cd770e1baffca32dbace40c3eadd0fb1ff9464a0e5c3d064db0b7dbff28c713038501d8b4ea0a7fe51879186fd6fcf677a32ffca30294cdf8981aca40a1ff945cb6d5c7d46ad8b19c3ff28b34a138d6984b0364677d517aa6a59ac0675e12acebaa2f29b8b231ecab9cb75d7545dfcbd623820d6ee323aea8bbcdd2bfbec0ad45ed) (by decide+kernel)

private theorem _AGE:WideCovered band13 12395683 13628338:=PRB band13 Z1.f511 12395683 13628338 (WB 240761101464 16 0x89068fed652cca0d7e7f9d9448347d71095b0073b3b1b061c1a3db524a878fdb9b339f0e051e537751a100ccc6cde87028efe4aa79dc0de59ff743814763b65349a7ab284bf2140a3a4d9696736b391cc1909fd1ccb514934948c7b91a84fe8e41dba3bc93be34615427f470c9351836a9b157ce60bfa37a66a88c098b88648f05fd1ba5e642c9774c3055682fa8db156a0d89b9e0ec32c17d46c56b501bebcb02add203ea358c0a7e634e37efd0901f51aa5a93e17850be5192) (by decide+kernel)

private theorem _AHI:WideCovered band13 13628339 14629870:=PRB band13 Z1.f512 13628339 14629870 (WB 240761169048 13 0x13a251abc37d325bbacdf3bee910e8b8e3c24f414cdef077ec78745a8988251281eb7388323c3a2c782491610073b76a371e1d15e509c83b1848da882a8d0e8acb5d43e9d0bbecad9cc6874551d811dab02db60b922342a2a1dc40e28b70bae02b11a1514d6e106cb7054d5d4668b0a8a4eee8340a361ea53bb4585451c56d18ef56cb4dea122c2a288f848c0d5783a49b29120d141c23c5cef030d120a3) (by decide+kernel)
theorem covered13:WideCovered band13 (AX band13) (tail band13):=(_Q1 band13 9699247 10142232 14629870 _ADB (_Q1 band13 10142233 10700780 14629870 _ADC (_Q1 band13 10700781 11317108 14629870 _AEB (_Q1 band13 11317109 12395682 14629870 _AEY (_Q1 band13 12395683 13628338 14629870 _AGE _AHI)))))
def band14:Band:=⟨8,54,4359,4735,8306538778321019⟩

private theorem _AMF:WideCovered band14 7077826 8811132:=PRB band14 Z1.f513 7077826 8811132 (WB 206366693528 16 0xb6dfb55eb549b11f0ce4f96dbf6a058a86497a17d46adb7ed56894f8046c2bbdc5b6fdab7fa9c735c84fa55b6cfb4ff5534103708f9e76d9f6923aa607e6a0ffe46db3ed07554b285cc1c117db67d9cc4a943e788304ccb2cfb2fbb5234b8f050ed5659f64bc6a3f6a5a082822cb3ec692546dc4ac0c652d967d8cf9a8bf554810f43b2cfb224f5121ea70123c2083f00ca201eb98a0051f8107e00f9c023058bfcb8e020fc0158002b8b07bac0a) (by decide+kernel)

private theorem _AMG:WideCovered band14 8811133 9645687:=PRB band14 Z1.f514 8811133 9645687 (WB 206366726296 16 0xceffa064bb48e88f932e77ceff9f845345e3ce9233b3caff9e307b4061cd9138eecaff9c7ae343e2bc903e2aceff99152345449b8f4365ceff906f6b557d3a8e48a0c6ef9d5acafdb2198d4ddcc6ef9c7a3afac5388c5317c6ef9b588afbb8378b5853c6ef99886b0162168a5d8fbaef9c037ab447b58962cabadf9bd402b1eea488e568badf9b9bf2aef8b3886806badf9b650aac5c5287eaa3badf9b2d5aa9f6d1876d41b6df9af202a78e3086efdf) (by decide+kernel)

private theorem _ANG:WideCovered band14 9645688 10672832:=PRB band14 Z1.f515 9645688 10672832 (WB 206366726296 16 0xdb1fa9240be7da1fa2dac0d71fa86db3da999ea1dffcd71fa7a263cbec9da0e537d71fa76923bebf2c9fea73d71fa6c113b2cb6b9eefaed71fa620a3a8206a9df4e9d31fa574e39d21799cfa25d31fa4b70b9161689bff60d31fa4ab2b8570379b049cd30fa4240b7dea269a09d8d30fa3756373a2b5990f13cf0fa2cf6b6b986498144fcf0fa204eb6200c397198acf0fa262535a5182961ec5cf0fa1c863538e81952401cf0fa12c7b4ec14094293c) (by decide+kernel)

private theorem _AOH:WideCovered band14 10672833 11186405:=PRB band14 Z1.f516 10672833 11186405 (WB 206366727288 8 0xe31faf4bfa39e86faab0e5df0fae52722fd4b6a9b621df0fad5ad226022da8bb5cdf0facd4aa1ca934a7c098df0fac0632148deba6c5d3db0fab25da0bc86aa5cb0edb1faa4fe203b439a4d04adb1fa9e3c9fb3518a3d585) (by decide+kernel)
theorem covered14:WideCovered band14 (AX band14) (tail band14):=(_Q1 band14 7077826 8811132 11186405 _AMF (_Q1 band14 8811133 9645687 11186405 _AMG (_Q1 band14 9645688 10672832 11186405 _ANG _AOH)))
def band15:Band:=⟨8,55,4286,4710,8495436101527662⟩

private theorem _AZL:WideCovered band15 7208897 8963366:=PRB band15 Z1.f517 7208897 8963366 (WB 206366693528 16 0xbaeffe30f548d9ff118a4d75bffbd48a872a3a2118f2eb7ff5b2d4fa9cec3e3a95d6ffe738a9cd6bc874868badffc68a5360e370d92fb75bff7994a61b2ea192a4edb7fecb4d4b1d24c2e5d4db6ffd39f2939b68854cbfb6dffa7eb521cf6f099bab6dbff5354a3c5cda113baadb7febc1d462c92c1e8005b67fd347a8abf24835116b6cff9cdb511ce4705a458083f80e4c01e788a094d04107f011a8022b20c0ea2b820fe0185002b1307ddd06) (by decide+kernel)

private theorem _AZM:WideCovered band15 8963367 9808111:=PRB band15 Z1.f518 8963367 9808111 (WB 206366726296 16 0xcf0fe4e6db4ba15f95a8efcf0fe44f1b471e1e94ab1bcf0fe4275343748d93ad46cf0fe3b51340ffdc92af72cf0fe308433e517b91b19dd30fd658135b456a90b3c9cf0fde2dfb39ad398fb5f4c6ffe02d62fa09f88eb820c6ffdf47a2f9dfc78dba4cc6ffddd63afa75268cbc78beefe0092ab58aa58bbea4beefdfcf32b32e448b3fb9beefdf8a52b028e38ac0cfbaefdf413aad14028a41e5baefdef31aa9ebe189c2fbbaefdef56aa6f540894411) (by decide+kernel)

private theorem _BAL:WideCovered band15 9808112 10847797:=PRB band15 Z1.f519 9808112 10847797 (WB 206366726296 16 0xdf2fefd203f7262fa58635db2feef02be8cd4ea48861db2fee3f33d8e80da38a8cdb2fedbe7bcc375ca28cb8db2fecec83bf217ba18ee3d72fec14abb22feaa0910fd72feb42f3a690799f933ad71feb22339a23089e9566d71fea608b8f03e79d9792d71fe9adf38601e69c99bed31fe8dd4b7ba5a59b9bead31fe80b6372c8949a9e15d31fe83afb683b0399a041d31fe7887b607fa298a26cd30fe6d6ab5a905197a498cf0fe5ecab525b2096a6c3) (by decide+kernel)

private theorem _BBM:WideCovered band15 10847798 11367640:=PRB band15 Z1.f520 10847798 11367640 (WB 206366727288 8 0xe31ff75e7a466187ad74d8e31ff61a3a3ad84eac7704e31ff5666a30a325ab7930e31ff44d1a26aa04aa7b5bdf0ff356b21e4383a97d87df2ff236a2145722a87fb2df2ff1b08a0bae89a781dedf2ff0c7fa03cf58a68409) (by decide+kernel)
theorem covered15:WideCovered band15 (AX band15) (tail band15):=(_Q1 band15 7208897 8963366 11367640 _AZL (_Q1 band15 8963367 9808111 11367640 _AZM (_Q1 band15 9808112 10847797 11367640 _BAL _BBM)))
def band16:Band:=⟨8,56,4215,4684,8697373051258664⟩

private theorem _BKG:WideCovered band16 7339968 9115600:=PRB band16 Z1.f521 7339968 9115600 (WB 206367774872 16 0xbee811792552b8dfc58be85f7408a92ea8a3efa2a5d7afba044b69540a25b142dd975d02209229dcddc89967abae810d4f14d62edc48b045d74085e12a609b6a22565aeba04319052b9d33102a4975d021be6a9289c88794b1bad810bc11484fe3c38a1fdd6c084c00a3c031a1a4f36eb6041af85195aab0c26b775b0207d728ad3c48592e9bad8100ea144ab71c2893b8234000fda01e390a12481413a0004e200898630823260830001ae802a9f0800e02) (by decide+kernel)

private theorem _BKH:WideCovered band16 9115601 9970534:=PRB band16 Z1.f522 9115601 9970534 (WB 206367774872 16 0xd318157899a8602fcc11b3698c0a9a9cd27fefa5c8a0b4c605321268f191b2c433da630285a4343584c9520bad3181369c5a132d5ca0feb698c092d78d2446ea4c7bc74c60406d5698e413243c1ba6301893db4894c8911d29caf812a4b57ba233c80e22e57c090edabdd6eda3c6d86fbe047dea56e726b1c34fb7df023a3aab46ac48d9a0bbef811a4fd586e89c68cccdf7c08d69aab6b34a32649efbe046f5e5553ae31831697dd023366aa7e6208b9842) (by decide+kernel)

private theorem _BLJ:WideCovered band16 9970535 11022761:=PRB band16 Z1.f523 9970535 11022761 (WB 206367775896 16 0xdf381b48ed01f3afea0c6a77ce06ad403f6b10ea730c5df381a881cfa2313698bf877ce0682203d9d92ca52efddb381984f8f2c666e90b8636ce0641fc3be003aa32d34db2818e8c4ec26da688b1436ca061df13a49218a12b6cdb28181060e6abbde80aa235ca05e65638f74369f29a4d7281729b4e0c91d678a3035ca05cb2737a3e549d27dcd72816c714dc6d48e709bdf5c60594ca3686ca29b2613d31815d458d7df3c66894bf4c605540a358b8b099244b) (by decide+kernel)

private theorem _BMO:WideCovered band16 11022762 11548875:=PRB band16 Z1.f524 11022762 11548875 (WB 206367775864 8 0xe7281fe0852a6dc3d81c65f3940f8d4e9212e3abcdf9f9ca07a9b6479bbeb5c6e07ce303c031a3278bcad361fe3281d5f65143af9d61a9d719c0e5b0c8787d6aacd15b8ce07187a4294af35466e5c67037bc9a0cd238a9328e) (by decide+kernel)
theorem covered16:WideCovered band16 (AX band16) (tail band16):=(_Q1 band16 7339968 9115600 11548875 _BKG (_Q1 band16 9115601 9970534 11548875 _BKH (_Q1 band16 9970535 11022761 11548875 _BLJ _BMO)))
def band17:Band:=⟨8,57,4147,4658,8904454736243445⟩

private theorem _BXH:WideCovered band17 7471039 9267834:=PRB band17 Z1.f525 7471039 9267834 (WB 206367774904 18 0xc2f833463d5382cc235a9eafbe0cc5e9548278f8ce880bef832e5a5508933a319a1afbe0cb85853bfa6d8be48cbef832e8694dd4ab22d8a4afbe0cba44531820b8ae098bee832c0e94b391aa297a7afba0ca57f528438989dca4bee83267c148e7322256aaafba0c8de351f85c788d8b0bae832005946b4f1a215adaeba0c70b7516118587d4bcbae831c241444df921d4b0afba0c4ca951227e386d0c8bed83082ad3d0178a193b3afb60b90b45046002854ada066820222003bee06111b9819e08039c00547e0823efe) (by decide+kernel)

private theorem _BXI:WideCovered band17 9267835 10132958:=PRB band17 Z1.f526 9267835 10132958 (WB 206367774872 16 0xd728380185ab600fcd4eef6b941bc600d4b2e3a6667ab5ca0dbaa569998fb312beda6306c3ee3479a2c979202d318352905a46285cb47076b8c19e566d24d7aa56286b5ca0c1dea6ada6b3290c4da630640e9b3e8908938232cf083468797c807bc93f1f678419d9fabe57f9a45e92b0c20cf4cd571408b20ecad861067b8cab5bcf48ff45cc30833e6e1591a69c7b931617c19e092abd8d8a3bc1a30be0ce6d95598e031cdcdd85f066e402a9eb108dec74) (by decide+kernel)

private theorem _BYH:WideCovered band17 10132959 11197726:=PRB band17 Z1.f527 10132959 11197726 (WB 206367775896 16 0xe3483eb90906c4fbeab747b8d20f97bb4082c1ea9d92ae3483dc95cfe0cc76a354db8d20f505a3ea7f1ca7d142df383ca3bcf6a046e9b353b7ce0f14ed3cb343aa5c95adf383be7b8ef740e693159b7ce0ed80d3b0c408a3c172db383ae380e97eb1e8af5fb6ce0e9324398bfb6a1b98adb383a46cce324e1682d65b6ce0e74a938302e49fb1a2db2839621cdec77ce7ab6bb5ca0e352a370edc29da9bad728386da0d9a594672971b5ca0e1d4f35d1be09ba1d2) (by decide+kernel)

private theorem _BZP:WideCovered band17 11197727 11730110:=PRB band17 Z1.f528 11197727 11730110 (WB 206367808632 8 0xeb383210d298e5e1ecbf2fbace0c6fa3a55f53eb1f8caeb38315af0929dd96c3d35b9ca0c3f47a3fded4aff0e2e7383095f48d0dacebbb3bb9d20c1628a290692ade8fae7483001b087d28a6b3941b8d20beb39a160340abe112) (by decide+kernel)
theorem covered17:WideCovered band17 (AX band17) (tail band17):=(_Q1 band17 7471039 9267834 11730110 _BXH (_Q1 band17 9267835 10132958 11730110 _BXI (_Q1 band17 10132959 11197726 11730110 _BYH _BZP)))
def band18:Band:=⟨8,58,4080,4631,9122773928262550⟩

private theorem _CIT:WideCovered band18 7602110 9420068:=PRB band18 Z1.f529 7602110 9420068 (WB 206367774872 24 0xc3085502b1540e0f47de9261842a81d4a956d763ce68b0c2154526543b6fb1d6c418610a9f56a9f367c8e329ec2f854d0654e744e46d78e617c2a4ffaa68af6e34ae6b0be151bf452fb51719503385f0a8702a950d5a8c2497bef85401dd4980ecc5d08adf7c29f010a3ff1a62c764efbe14f80851b67b11534237df0a7cb028b40788a168fbef853e32d44357bc4c986df7c29aaf8a1c16da243e2efb6149c5e4ed3a2b1118137db0a3b37a774495878506bed850bb293cd432c33f015d6c28ad62988bb5215dbfaeb6142efc4c4670908dff57db09c08a26de9648368f7bac85035992a3299c130f98334200b50010d4ca056bbc16a1005b1008672300a7d60850801f880299107c37dc) (by decide+kernel)

private theorem _CIU:WideCovered band18 9420069 10295381:=PRB band18 Z1.f530 9420069 10295381 (WB 206367774872 16 0xdb385a63c9af86fece8c2aeb942ce108d62657270454b5ca163ecd6a2ef5736149dae50b1eb8b4adc1a9a034ad72858624da563eccc7e236b942be668d237aa25fd50b5ca156f5069de14f2ddc7db6709a42336cdfb695e73acf185676897d4282ca701be78c2afeb4be878124f64d31c61587b8575606725a4618e10abeb4ab7c453924eaec70855c9355a523948e59663842accecac57c86451eab1c2155ae255cf3a32188518610aa772aabad009040a6) (by decide+kernel)

private theorem _CJU:WideCovered band18 10295382 11372690:=PRB band18 Z1.f531 10295382 11372690 (WB 206367808664 16 0xe7585129d685d889f5b1125ceb0a1e3050722fbab2063f9d6142639a059f0ed5bd45f1a4281f133f9ebecaa7387e3484fef267d0e9f752d907c6909f8fe8f67f9aaa195ff8d213de911e5ea9cd3af3defa427968b3be7b98a65777df484edf02763a56f4aa0e9be909da18ce904d1a9125c77d213a2f51cc65a2d1a136ef9c27217e38d8934a23b69db384df4887046fc74268cbb6709b826cde65d8a80b5876ce136fdb1b79df0cf932eed9c26be2a36704409e1f59) (by decide+kernel)

private theorem _CLD:WideCovered band18 11372691 11911345:=PRB band18 Z1.f532 11372691 11911345 (WB 206367808632 8 0xef48544c469ceda5ed702c7bd214ff4b2673c86b4b9aeef38538240968ccd6cecaabace14c1d3a4d4d44b2aba6eb48529816903e7aec6928bad6149399235d632b09d9eeb5851e7168ad0086be5a6b9d6145fa3220b428ae8f96) (by decide+kernel)
theorem covered18:WideCovered band18 (AX band18) (tail band18):=(_Q1 band18 7602110 9420068 11911345 _CIT (_Q1 band18 9420069 10295381 11911345 _CIU (_Q1 band18 10295382 11372690 11911345 _CJU _CLD)))
def band19:Band:=⟨8,59,4016,4604,9371349841764829⟩

private theorem _CUF:WideCovered band19 7733181 9572302:=PRB band19 Z1.f533 7733181 9572302 (WB 1305879402648 29 0x18e30ee72faa97428920fce63843b86fca9acea2462b118e10edbbe2a3f8a89105ba63843b55a0a84e5624202c58e10eceb229e76488ffba761843b1fa6a7025e23dda758610ec096a9997f88ef19361843af8eea5aec6239b2258610ebef0a93cc888de77f61843b00dea4317a23589d585f0ebafd28e88188cdd6c617c3ad146a31b8a231618985f0ead13a8a58d88bd358617c3a9486a2123222d39398df0e5d362934b678ac944617439e60a9cdbd9a26fcc585d0e68bf272839688b51d6174393e4a9cee99a1eac2985d0e114827aa84686a0f65f6c39200e9732dd6165b8d7db0e2498a6011f5848ccf5d64392e9493554d20e0af375b0db86ca6044948278a85b64393e08924f74e05ba556d90e446c248549380e98b5b6438de9291e5d0e0192040d30c08a280daf427fdf77034430138401d4e05fd69b40bb0c030600427d07e5059) (by decide+kernel)

private theorem _CUG:WideCovered band19 9572303 10457805:=PRB band19 Z1.f534 9572303 10457805 (WB 1305879402616 16 0x6d9c3e5da4da3f664fc966b6ce1f0a7a6c0f2127a22e5b670f87db3582d993afd4cdb387bd291a937e49c74926d9c3d93a6d3faa44db53f36ce1e90ec69c35a26981adb670f211eb4f97f132acafdb386d2169bf9fa3984c436d9c3a2a56d251694ba11834c61e297b5f3b06658e0759630effa42bde7c12a5c12cb1877cb115d50f094a8ff658c3bcb5aadd47c4a11fab1c61dd7ec567eba24e7bb18e30ee4b0ab08a012633c4c718772cf95685989294d8) (by decide+kernel)

private theorem _CVG:WideCovered band19 10457806 11547655:=PRB band19 Z1.f535 10457806 11547655 (WB 206367808536 16 0xeb6873170e88741d60680fd6d0e565c90c507abca7cf9d61c94bf210238d70ff073ac38f42040d704ad15cce75871bb047f6d3b581771ceb0e2c4e0fb032eac06978d61c41d51ee5b6d4fbc8f1ac38543b3cd4c7a8ed7de358708d7077bc954fc6d5c6b0e07ef4ec62e29b655f8d21bfb839d29fb52e7a1efa437cbcb398ea8a4c52fdf486f616c718e05477639be90de8df4e061868ac4237d21bc0ac1bcc7c50d37a6fa4375bb1371b63a09ce1) (by decide+kernel)

private theorem _CWU:WideCovered band19 11547656 12092580:=PRB band19 Z1.f535 11547656 12092580 (WB 206367808536 8 0xf35876da7ea1ef0b710949e690ec8ef93c94eeddea47bd21d6d6326ad57db383ef7ac3a91e34b957cb56669ef5874c72093d37768b8added0e89b3d21cf42cd490bada1cf4e82380bdd9241775b439ac214590abb13e1b) (by decide+kernel)
theorem covered19:WideCovered band19 (AX band19) (tail band19):=(_Q1 band19 7733181 9572302 12092580 _CUF (_Q1 band19 9572303 10457805 12092580 _CUG (_Q1 band19 10457806 11547655 12092580 _CVG _CWU)))
def band20:Band:=⟨8,60,3953,4576,9632706922308050⟩

private theorem _DEO:WideCovered band20 7864252 9552287:=PRB band20 Z1.f536 7864252 9552287 (WB 206367842424 19 0xc71885ff0314e7b0d91c19fc71885fe3214d36cd913b0dc7188600be14b799d90b47cc70885f32f14a36cd902debc70885e63d14951858fa759c70885d68e14811fd8f20c7c70885c583146d03d8e9a35c70885b398145b8d58e13a4c30885a251144ba758d8d12c30885a00714373fd8d0680c308859e5f14226158c7feec3088598241416a3d8bf95dc30885977814013fd8b72cbbae897e5a64f2dd148aec39bae88cba752a7bef489df16be56e98e9820d144b88d1f2ba26639a7b0c9fce2849d650415824f490837d218068d704c8800a660039e407c3449) (by decide+kernel)

private theorem _DEP:WideCovered band20 9552288 10206832:=PRB band20 Z1.f537 9552288 10206832 (WB 206367774776 16 0xdf489a43a1aad3e26ef9c37d225e7c46b939a9ab14cdf4893e191b1befe6690a73ca268fc45900aa989706cf289a06cd62302a6041d33ca2673115815ec9789e2cb289994f15ec7525c0d472ca265565573afa967cbfcb289943dd5afc0257d8b72ca265348563fb0956f9bcb28992f4d57a4fa53a42b2c6263e6f5586bc946278cb1898c189548d1a4f6f9b2c626233854d51a935554c718984e2551bf124b3b0f1c62602c154087e924831) (by decide+kernel)

private theorem _DFK:WideCovered band20 10206833 11309223:=PRB band20 Z1.f538 10206833 11309223 (WB 206367807544 16 0xe768929374fb2f2359214fced124921dee57aeae0e139da248347bcd0c4d53b3073ac48db557813cfa9693de35891501aec6f8f50b835c6b121e72dd2af8e9d3bdb8d62439d9397453d320e9f1ac484d1171bd13a534afe3589047dce13a1f484f19be911fc071bca7668c69a37d223e889b70c45d106a2efa447d2ce6cb3fda10021df488f5850d816db3fe5fdbe911dfea1adff9e7b976b7d223a170355e1bceec5befa446f70f6a4d8e9ccb93) (by decide+kernel)

private theorem _DFP:WideCovered band20 11309224 12273815:=PRB band20 Z1.f539 11309224 12273815 (WB 206367808536 14 0x3dda2659ea29d9325da44bfbac4c57a0518dc3ba3b74f35898081e9f4be3725ca1e6d12ec1c536f07ee084b7cda25bd07a5f9965b8a04f9b44b35284a6a08b606e6ef7895d23e916ef769f385def12ad41d1cd696cfb27fbde253ed222e318d96fbdf7b44a43dc448b19b1d259eb689412a486a561618a6bd6d127838907b6e6bee04bada24da0820758dd7557775b4497cb03fc788ad9dcb) (by decide+kernel)
theorem covered20:WideCovered band20 (AX band20) (tail band20):=(_Q1 band20 7864252 9552287 12273815 _DEO (_Q1 band20 9552288 10206832 12273815 _DEP (_Q1 band20 10206833 11309223 12273815 _DFK _DFP)))
def band21:Band:=⟨8,61,3892,4548,22720554753899673⟩

private theorem _DKT:WideCovered band21 7995323 9493512:=PRB band21 Z1.f540 7995323 9493512 (WB 206367908984 18 0x31c628620ac0a3ed3ac86e04638c50c3e26146548d9053eec718a186b0c28a8fab1f97ab8e31430d6f050eb4f63d0eef1c628616350a152b6c75dd0e38450c06ac14196558e3388c708a17c250281fefb1b56dd8e1142ecaf05003bd6348d531c2285c0ad09fc7fec64d9ddf7c593b0d4e27b74c8c1321bae8a6c012ca7561671605dd75d14708a30afa8a0e27caeeeba289f2030f5c41dc471445d7450f816e1819e7387d254ba368158fbc24a27050d844371cc01daba8363fd660a0552baa0820220032da383f2043d754103c992063ce787c2021) (by decide+kernel)

private theorem _DKU:WideCovered band21 9493513 10050978:=PRB band21 Z1.f541 9493513 10050978 (WB 206367774744 16 0xcf38bb6565600ccccaed1679c5db41caf04266356233ce2ed63c570bc1309adf9e51764772b58d497c555cf28bae581590914b9e9de7945d55a2abcf525ad48b3ca2e99a855759b2c5a119651744aa2a8cce95a4eecb28ba0269528d44a8e6ae5945cff48a889025252ef2ca2e81b953c785281943963173a5729bfe0938488cb18b9950d4ca7c497e37e58c5cab12a5ba5649d1572c62e45395298a523d8779631718b7a91d19916422) (by decide+kernel)

private theorem _DLN:WideCovered band21 10050979 11061385:=PRB band21 Z1.f542 10050979 11061385 (WB 206367807576 16 0xe768b25146e9b7d2a8c889e768b1efc4e6d1faa7b856e358b1869ee3f222a6a822e358b134e4e1138ea597efe358b133fcde4e5ea487bce358b0d97cdc4c3aa37789e358b0746eda6e26a26756e358affebed8bd6ea15722df58af6d8cd74de6a046efdf48af10a8d6cbd09f36bcdf48ae8984d6b6249e2688e348ad3eaed8b9149d1655e358a9efd6de23459c0622d338ae0966b2d3909af5efcf38adeaeeb1f6249a6dd5cf38adc788b0e95899e5bc) (by decide+kernel)

private theorem _DLS:WideCovered band21 11061386 12176317:=PRB band21 Z1.f543 11061386 12176317 (WB 206367808536 16 0xf778b93ee49c695573977be6f1712615319122e2ee2bce22df9c0254c9a5bd5ab79c45bc0dc48f1d0b69b23f378b6f6ac8f0a476b15e1def16ce31918c5fad1eaf7bde2d77f9225f9a59b54577bc5acd20436995b25a56ef78b5215684768d629447d6f1694c050439e6c0e7c3ade2d09b41ff080d794de75bc59fe3f3eca10ae1989eb68b393927bae6f5a12adced1664db0f394b6afe48f9da2cad209df91055747873b45950e13b04c8a9d8bc) (by decide+kernel)

private theorem _DLT:WideCovered band21 12176318 12455050:=PRB band21 Z1.f543 12176318 12455050 (WB 206367808536 4 0xfb68bc22b0ad82a97c1915f6d1769dd151cf56f3f15fdda2e9f7429196eddf6127bbc5cf5ec500d38badbf0) (by decide+kernel)
theorem covered21:WideCovered band21 (AX band21) (tail band21):=(_Q1 band21 7995323 9493512 12455050 _DKT (_Q1 band21 9493513 10050978 12455050 _DKU (_Q1 band21 10050979 11061385 12455050 _DLN (_Q1 band21 11061386 12176317 12455050 _DLS _DLT))))
def band22:Band:=⟨8,62,3834,4520,21988741718642783⟩

private theorem _DPN:WideCovered band22 8126394 9465268:=PRB band22 Z1.f544 8126394 9465268 (WB 1305879536760 18 0x658c60ca2d8142fecd906db4658c60c719a142404d8fe412658c60c3e2e14195a58f5a70658c60c27aa140b14d8ed0cf638c60c0d7213fe2858e472d638c60be62413f8ad58dbd8c638c60bb26213f72858d33ea638c60b69d213fbd7d8caa49638c60b1a4213fbe158c20a8e38c60a80cc14135058b97065d74636c0a64ff33f48b0d655d7461d1e562ad75cc89fa215d74614c2a61e38dac88e6de5d74610408217d06f487d39b5f7468836c0d88dbcb86c0585cd310826ea0c8c07a8499d15b64307237c0beb111804cc5575c1044018065a2987e263f) (by decide+kernel)

private theorem _DPO:WideCovered band22 9465269 10029004:=PRB band22 Z1.f545 9465269 10029004 (WB 206367774744 16 0xcf38dc3b8558f204c83e6679c6e032aaba34261f8af3ce3700305565192fe9139e71b7fcd2a7b52976ae8cf38dbda895260e4b70a367946dca88a85e66595e933ca36d4cc53dc2d2b9c079e51b619f29c4c6954462cf28dac16d4cdcb4a5d60e5946d3abaa5c47650c47f2ca369bb2527499274efb9651b4c33290ff0931ddccb28da566547291c94a1d65946d1db4a2f8fa482a632c6367c63513c712301ef9631b339fa8799e90f755) (by decide+kernel)

private theorem _DQF:WideCovered band22 10029005 10945075:=PRB band22 Z1.f546 10029005 10945075 (WB 206367807576 16 0xe768d268b4e1540ba70233e768d204dedf7463a5eef1e368d182a6dcecd7a4dbaee358d10148db702ba3c86be358d0ef68d925b3a2b527e358d0a478d86fd3a1a1e4e358d044a0d7a900a08ea1e358ceaf0edabc749f7b5ee768ca5caee1e2469e681bdb48cf3c68c157fd9d54d8d348cec24cb1ed089c4195d348cec38eb0b5b09bb7f3d338cea5ccafe7bc9b2e52d338ce86f2af197c9aa4b0d338ce66d0ae4a989a1b0fd338ce4532ad7adc99916e) (by decide+kernel)

private theorem _DQK:WideCovered band22 10945076 12072549:=PRB band22 Z1.f547 10945076 12072549 (WB 206367808536 16 0xf788d90380930457706ccbe711b0ab651f53b6dc8c8fce235fdbf2328915b07eff9c46bb2a644e7b8b4fc9cf388d6df22875beb67d2b3df11ac9a51096d86cb585bbe23582e1a0898b58e16977bc6acd744018b9b0af8fef78d519327dee1b5f3899d6f1a942dcf8037eba242bade35197c9e6d8956bae3f5bc6a087f3c12cdac6283eb78d3ab7e76ac6f569e81ced1a661ace9bf3aa8eff79da34b31e9cdbf9d4945d73b469624b38d80ea81576) (by decide+kernel)

private theorem _DQN:WideCovered band22 12072550 12636285:=PRB band22 Z1.f547 12072550 12636285 (WB 206367808536 8 0xff78df0796b46fdd81a0fbf6f1bbff0d5df42efef4ebede37443caa8832df54fbfdc46e3bcc52e88bbd96b4fb88dba14aa176557906e3ef11b5be8d3b36daedc0bbde2368e3d265866dd2e75fbc46cd3454b1709b949a8) (by decide+kernel)
theorem covered22:WideCovered band22 (AX band22) (tail band22):=(_Q1 band22 8126394 9465268 12636285 _DPN (_Q1 band22 9465269 10029004 12636285 _DPO (_Q1 band22 10029005 10945075 12636285 _DQF (_Q1 band22 10945076 12072549 12636285 _DQK _DQN))))
def band23:Band:=⟨8,63,3776,4491,21757330375329369⟩

private theorem _DQQ:WideCovered band23 8257465 9397478:=PRB band23 Z1.f548 8257465 9397478 (WB 206367908952 16 0xcb18e198a8427bb45e3d939b2c63864c6509e9f0f8ed9bdcb18e18e714279835e393a4f2c638622a009e39338dc36acb18e1811ec278caee34e1032c6385daa709e61af8cad17bef8d2ccd8d9cd39aa3087b6eba31d1d1a2833ac58b0b9abae8c3dee38562f7e627d522eba30b00650f256fd88def5bae8c228c802fe35561f228adb6307039f09cf05d86b24fb6d8c1737c420dcae6166ff6db63052a980730e7d8485aab6d8c127d4819ff5b60dbd5c105704647c0726bec825904) (by decide+kernel)

private theorem _DQR:WideCovered band23 9397479 9967485:=PRB band23 Z1.f545 9397479 9967485 (WB 206367774744 16 0xcf38fd2235519b94c0bbee79c7e8d92a7eaaa5e31533ce3f45da5381272e02579e51f9a9f299579967601cf28fc8ead4b53bcaf56c67947e21daa4fdce557ebb3ca3efcc85228c729a90b9651f737428e92e94495bcb28fb7b3145edb49df1965947db47ea248724ccc232ca3ed3f050e161254fbf9651f6754284a56921cb5cb28fb1ba1410ca48c8c6658c7d640ea0156e44198b2c63e9ad74fd55920f6739631f405627d1cc8ff00f) (by decide+kernel)

private theorem _DRC:WideCovered band23 9967486 10751245:=PRB band23 Z1.f549 9967486 10751245 (WB 206367807576 16 0xe768f1ee1cd9e97ea40d0de368f15b32d8df18a2f6bae368f0fe4ed7f8eca1e067e368f05212d81978a0ca14e768ee9fa4daeea09fb3c1e768ebef7add36f99e9d6ed748ef9e72b1edc89d871bd348ef7840b0f35c9cfbf2d348ef5d76afecac9c70c8d348ef5ac2aee1549be5a0d348ef5292addeb89b5a76d338ef31a4ad0acc9acf4dd338ef0f58ac35d49a4423d338eeeb78ab5f7c99b8fad338eec5b6aa8730992dd0cf38ee9dbaa9ac4c98a2a7) (by decide+kernel)

private theorem _DRD:WideCovered band23 10751246 11891259:=PRB band23 Z1.f547 10751246 11891259 (WB 206367808536 16 0xf388f8beb48995f36ae477e711f055c50dfa16d16fa3be23de531211a74d9a2caf7c47b7d4f40ebb9b22f42ef88f6c1e27f73696231dfdf11ec8594fac41ac00a73ade3d6fe11ed4f2577624f5bc7a9af03ca238add5f6eb78f52812778c05597f49d6f1e975e8ec019eaea547ade3d116a9d1beb55497f73bc79e3b339715ca97cabe768f37e7a71570f50ccb3ced1e6c638dfd4da9d401b9da3cbd921bb5ea531cd9f3b4793e3e36ec89a52360) (by decide+kernel)

private theorem _DRE:WideCovered band23 11891260 12817520:=PRB band23 Z1.f547 11891260 12817520 (WB 206367841304 13 0xff88f19424609b1ec39470ff88f0fb645d9ecdc27e1dff98f085e05ab3a6c167caff98effeb6581053c05177fb98ef7a3a557fbbbf3b24fb98ef116652fde6be24d2fb98eea9da50e316bd0e7ff798ee3e664ed958bbf82cf798edd3814cd874bae1d9f798ed8f3b4af1c0b9cb87f798ed36cd494ee3b8b534f398ece72147e2f8b79ee1f398ec8de4464a8ab6888e) (by decide+kernel)
theorem covered23:WideCovered band23 (AX band23) (tail band23):=(_Q1 band23 8257465 9397478 12817520 _DQQ (_Q1 band23 9397479 9967485 12817520 _DQR (_Q1 band23 9967486 10751245 12817520 _DRC (_Q1 band23 10751246 11891259 12817520 _DRD _DRE))))
def band24:Band:=⟨8,64,3721,4461,16176827029209600⟩

private theorem _DRF:WideCovered band24 8388536 9361004:=PRB band24 Z1.f550 8388536 9361004 (WB 1305879503992 16 0xe594818367027e64db1dacd9cb2902d93d850372363926eb965205055f0a273ae46de84f2ca409d01e141b29b8d305761848198270248e8e519474ebef8bc7d5fa5419a26305bd575d19bd1fb249defc457ec9aeba31ec5ca28d54a089e4305d7462cc0183ab9f6111959abae8c46d4985d9d1621ec5ad6db1873ce609a7d98434c042db630b81ae0f8c9e0857ea55b6c614dc401bb2eb108ca84b6d8c2574a83246b820d2f7d659184372c05beee041193e2cb230791740a8f658811919) (by decide+kernel)

private theorem _DRI:WideCovered band24 9361005 9937281:=PRB band24 Z1.f551 9361005 9937281 (WB 206367774744 16 0xd3391d8c7d4bb22cbd0c0e79c8eac32a50e5e5c53433ce4751d3521fdd2d103d9e723a5b928eb6e95fb6dcf391d218145af6cab75e679c8e73c6a22bde53882f3ca47266250e7e528aab39e52387332850b793c8a8cf291bcedd4171dc99dfb67948daf26a032aa4abd173ca46c7cd4ffd812445279e5235d1327e14c9195e2cb291aaa353e30448849965948d1f049f200a41f2032ca46763a4f701b1fdf9f965232a6e27b06a8f631d) (by decide+kernel)

private theorem _DRJ:WideCovered band24 9937282 10621611:=PRB band24 Z1.f552 9937282 10621611 (WB 206367807576 16 0xe7690fdcc8dd8490a212abe7690fb9f2d6b1aea0f948df5910f290c134e59fdfe5d7591060c4b0ca649ec682d74910408eafd3309e39d1d749101ad4aee2d89dad20d7490ff7c8ae1dd89d206fd7490fced0ad2a389c93bdd3490fa3b4ac33409c070cd3490f8b0eab6b7c9b7a5ad3490f8612aa6cd89aeda9d3490f8316a967389a60f7d3490f6780a8b88c99d447d3390f4276a7fca8994795d3390f1a4aa7360098bae4d3390eef72a66da0982e32) (by decide+kernel)

private theorem _DRK:WideCovered band24 10621612 11774166:=PRB band24 Z1.f553 10621612 11774166 (WB 206367808568 16 0xf39918604a825211b3a8d6f38917c4907fda39b28f73ef8917350a7dc0dbb17610ef8916ed727b9a01b05cadef891685067995bbaf434bef89160bae77fbfbae29e9eb8915797c7609f1ad1086eb79151b86747b85abf723eb791507ce73019faaddc1eb791489f6719039a9c45eeb791412b0708f79a8aafbe7791376e46f3623a79198e7791309706e6d8ba67835e76912c0786de05da55ed2e769126ebc6d3902a4456fe76912063c6c98d2a32c0d) (by decide+kernel)

private theorem _DRL:WideCovered band24 11774167 12926721:=PRB band24 Z1.f554 11774167 12926721 (WB 240727579672 16 0x81d4895ce9b0db06629f80c0ea4486b8d7ae647109679ff5222e60eb7280b861876ffa910dc5758cc29c1f2d87fd48834cb2b0454e06cbb3fea43fb4e14f0acaff004df7521ee8f2a329737d4d60fba90ef8d84f3614bd8d4d7dd4875695a6ad075e39f5beea43912712dfc7aed6a21ef521bbd3e93715b74824cf7a90d98f9480af1b927c37bcc86a401a339d15c0730bde6433da4d14646adbd3f9e7321940f287602d6bb736f3990c7417423bc8b4c238) (by decide+kernel)

private theorem _DRM:WideCovered band24 12926722 12998755:=PRB band24 Z1.f554 12926722 12998755 (WB 240727579672 1 0x103991357e3655088c65863) (by decide+kernel)
theorem covered24:WideCovered band24 (AX band24) (tail band24):=(_Q1 band24 8388536 9361004 12998755 _DRF (_Q1 band24 9361005 9937281 12998755 _DRI (_Q1 band24 9937282 10621611 12998755 _DRJ (_Q1 band24 10621612 11774166 12998755 _DRK (_Q1 band24 11774167 12926721 12998755 _DRL _DRM)))))
def band25:Band:=⟨8,65,3667,4431,20439130956430587⟩

private theorem _DRN:WideCovered band25 8519607 9357019:=PRB band25 Z1.f555 8519607 9357019 (WB 206367908984 16 0xcf292175dfc27630c91d8db78e324355c0048e306e38e28b1c2486927609157cdc6d534638c90d0c74128484a8d1c2fc719219f58824fae3519aa278e324338a0849e6d8a3237db1c64866232093c0c946236cdf7c693f4b8b8ea2798bffbcbae8c6fa0d08c7113115c69575d187e3b28a02e502271b62eba30afab70dc5e6c445532dd74611916616345d8878df2b6d8c1cf53824f79910ce3016db182f15703bf370215543adb6305515406c1914421c4ddb6c60997da0c54fe8831c28) (by decide+kernel)

private theorem _DRO:WideCovered band25 9357020 9939567:=PRB band25 Z1.f556 9357020 9939567 (WB 1305879402584 16 0x699c9f3986a38f4a97aa6f699c9f0caaa317aa971c36699c9ed9b2a2947a968dfc699c9ea0bea1fd8a95ffc3699c9e8676a19ad295718a679c9e7130a0f65a94e350679c9e5048a0a762945517679c9e365aa00b4693c6de679c9e089e9fddb29338a5679c9de4149f54aa92aa6c679c9d98a29f6bbe921c32679c9d3a569f87aa918df9679c9ca704a0047a90ffc0e79c9b27bca2a05e907186e79c9a3258a330898fe34d67949c4d009ce9088f5514) (by decide+kernel)

private theorem _DRP:WideCovered band25 9939568 10522115:=PRB band25 Z1.f557 9939568 10522115 (WB 206367807512 16 0xdb593111a6b1292e82380f6d64c39482c06729fffcad75930bb44af37027dc6435d64c24452b87fc9ee357d759308840ad386679547b5d64c20d2ab057a9dc6e4d759306dd4ab451e74e2af5d24c1127aa98e39caa72d749301de2a9afe27070e75d24bfd112a3da59b8e00d7492fc45ea818566bff1b4d24be884a9d9a09a718dd3492f990aa679da678d534d24be34da9717299551ad3492f8782a4cd4a631b874d24bd9eea90fe99838a8) (by decide+kernel)

private theorem _DRQ:WideCovered band25 10522116 11650802:=PRB band25 Z1.f558 10522116 11650802 (WB 206367807576 16 0xf39937fb72f81a5fb1c6f2ef993764fef4281bb0aa7fef8936d23ef038ffaf8e0cef8936be86ec5eefae719aef89363e0ae96bebad5528ef8935b400e692b3ac38b5eb89351b32e3d2bfab1c42eb8934b8dae1a5dfa9ffd0eb79348818dfdd6ba8e35eeb793456fcddd1f7a7c6ebeb7933aeb0dc34b8a6aa78eb793308cadd2284a58e06eb7931810edf57a0a47194eb792ff02cddae2aa35521e36931e952c305f9a238aedb59313830b20a60a11c3c) (by decide+kernel)

private theorem _DRR:WideCovered band25 11650803 12815898:=PRB band25 Z1.f559 11650803 12815898 (WB 240727579672 16 0x81dc98f200accfea61c70d40ee4c530cd5bcecf09c69dff72616e36a8b46b82aa68ffb9304fb651e37ac038c27fdc97eada27e4c35f8e283eee4bda15137d3f6f7ff75f7725ddf9c97e05b79c6d4fba92eaa7f4a1467bbc6f87dd49723a0a438e0dd55433dea4b78dcd1b53b2e6384def525b13408a75e370e340f7a92d538143cfc8b7552e7bcc968001a142fa5b1c5e3ce64b2aa4104fb0ad47125e73258d326803b9f67ffacf3992c45bd3f05f0b2e364) (by decide+kernel)

private theorem _DRS:WideCovered band25 12815899 13179990:=PRB band25 Z1.f559 12815899 13179990 (WB 240727579672 5 0x107a93551b46ab114c91c5683d49a51dd33711363fff241ee4cf6f698d1c6f1b8dc607726635cebfa3798b8dfd03b93266cc5c7be3c4aa8c) (by decide+kernel)
theorem covered25:WideCovered band25 (AX band25) (tail band25):=(_Q1 band25 8519607 9357019 13179990 _DRN (_Q1 band25 9357020 9939567 13179990 _DRO (_Q1 band25 9939568 10522115 13179990 _DRP (_Q1 band25 10522116 11650802 13179990 _DRQ (_Q1 band25 11650803 12815898 13179990 _DRR _DRS)))))
def band26:Band:=⟨8,66,3567,4400,20887884212447001⟩

private theorem _DRT:WideCovered band26 8650678 9331499:=PRB band26 Z1.f560 8650678 9331499 (WB 1306953278584 16 0x64ca506faba092beea473195b265283758204961812386d29932941b5e5c24b5d691ba6d4c994a0d690612657ac8d8b8964ca5067db2093ce0a46a1d4326528324a704a25ff233ef1f9729415793025eec271967cfc594a0cff3e123d8da8c6c07e2ca5065ad109243cd461213af5f1a8da90ada3c8062f711972e8c6c615879f28f1157986b97462032f22491448899d405cba30b99f60d03c48443edf2e5d184b064854dab021d78f16ad8c1dbecc2203a210c7d74b56c60cd4800e8a9d0851f37) (by decide+kernel)

private theorem _DRU:WideCovered band26 9331500 9828314:=PRB band26 Z1.f561 9331500 9828314 (WB 1305879402584 16 0x69a4afba449f36b095f7da69a4af93609e902095681a69a4af4d2c9e6bb494d85869a4aee88a9e85e094489769a4ae479e9f23bc93b8d669a4ad1492a12a78932915e9a4ab0536a47d47929953e79cade6b69bdc76920992e79cad20749cf8a69179d1658caec1ec90e51990ea10658cae8a76909975905a4f6594ae8b089336c48fca8e6594ae726a930ddc8f82ae6594ae56e492e9608f3acc6594ae372a92cc048ef2ec6594ae11b492c2448eab0b) (by decide+kernel)

private theorem _DRV:WideCovered band26 9828315 10417133:=PRB band26 Z1.f562 9828315 10417133 (WB 206367807512 16 0xdb59520054a99a227bcfb76d6547262aa272c9e642cd759519b9ea7d08a7751af5d65462e9a9c0f39d44aad759517c42a635ea72d3a75d6545b67a9597d9c2527d759515638a46ab66e559b5d25449f4a8f5199b05a5d74950f5f8a341f269d78f5d2542ff7a8ad0299e623d74950847ea22b7e65598b5d2541a31a8602b98c6a0d349504f24a0e44e60db7f4d2540c2a281aac97a71ed349500e649ffb665c5d774d253f9b6a7e63696879b) (by decide+kernel)

private theorem _DRW:WideCovered band26 10417134 11300360:=PRB band26 Z1.f563 10417134 11300360 (WB 206367807576 16 0xef89578bdae28527ac6e08ef89572fb8dfb2efab4e86ef895695d6de9cc7aa2f04ef8955c5c2dd374ba90f81ef8954da62dded10a7efffef89534c22de7930a6d07def8951ac96decef2a5b0fae76953ca94c2fbfda49179df69531824b1359ca371f6df6952e7dab039f0a2e236db6952b576af3cbca25275db69529b14ae3d78a1c2b3db6952902cad0408a132f2db69528568abfb1ca0a331db59525b50ab2e98a0136fdb59522eeeaa640c9f83ae) (by decide+kernel)

private theorem _DRX:WideCovered band26 11300361 12477997:=PRB band26 Z1.f564 11300361 12477997 (WB 206367841304 16 0xffb950b0b24b6744be662dfbb9503056497dafbd46acfbb94fbba047d1f2bc2729fbb94f7e164631f8bb07a7fbb94f139b44aab7b9e824f7a94eb2e8435a83b8c8a2f7a94e4a5a41f4afb7a920f7a94e223540990ab6899df7a94dd19e3f942db56a1bf7a94d73da3e638cb44a99f3994d1cc23d674cb32b16f3994cfed63c6e95b20b94f3994cc0383b7268b0ec11f3994c76953abdf6afcc90ef994c1b4939db91aead0def894bde3439379fad8d8a) (by decide+kernel)

private theorem _DRY:WideCovered band26 12477998 13361225:=PRB band26 Z1.f564 12477998 13361225 (WB 240727579672 12 0x85dcac76e837bcf665f024c2f256036adac7e0b2b031e1792ae2fe6ce52bb93428907c956189d630b98c881c383e4aab3aaafc2a763b12041f2552a15571f54f190afe0792a7c8eeb2c7c18a467903c9533215569dc5c403b981e4a9590929f3cc61721bc0f2548856146bd0f0712d5ff92a325249f0c97814a66ffb95120d04d2930bf85b0) (by decide+kernel)
theorem covered26:WideCovered band26 (AX band26) (tail band26):=(_Q1 band26 8650678 9331499 13361225 _DRT (_Q1 band26 9331500 9828314 13361225 _DRU (_Q1 band26 9828315 10417133 13361225 _DRV (_Q1 band26 10417134 11300360 13361225 _DRW (_Q1 band26 11300361 12477997 13361225 _DRX _DRY)))))
def band27:Band:=⟨8,67,3516,4369,21795447504693493⟩

private theorem _DRZ:WideCovered band27 8781749 9358241:=PRB band27 Z1.f565 8781749 9358241 (WB 1306953278584 16 0x64ca5871e1809195264765d0b2652c3865b848b89123a0bf5932961bbe20246d7f91c74b2c994b0d993412417bc8df1b464ca586a55e092675646d487f2652c32666049cff723581ab9729617809c25429491a2f8dcb94b0b9ba61294b8b8ccf2164ca586a0a109082d146433ef1e32c352d384791c6630f7638f1961a129423d2b7317ea68bd7c6ad23c4ba849d88bac8f5cba31a18641c53c304544fe2e5d187867d0816b962259dad72e8c2f141032f2f211089b0b96c612464e13f43f0872246) (by decide+kernel)

private theorem _DSA:WideCovered band27 9358242 9897540:=PRB band27 Z1.f566 9358242 9897540 (WB 1305879435384 16 0x69a4b827e84f396825c1911a692e0425d3c27689674fb69a4b7f4884ee46a2578ec9a692df44853b38f095526969a4b7a1824ed0da2530481a692dd6cd53c0408942fd7e9a4b6e3184f948e24e7a3ba692d7e1c14471f4930d46e9a4b5aa3950eda2e49eff1a672db9b29363e8291eab36594b7a2a647b5cc64565a99652de21751e248990c821658cb76a0c476142640db5d9652dd63fd2363408fa58e6594b7465348d8f423d73a99652dcdc8922fa208f1445) (by decide+kernel)

private theorem _DSB:WideCovered band27 9897541 10492630:=PRB band27 Z1.f562 9897541 10492630 (WB 206367807512 16 0xdb6972d3d0a92b0e806b5b6d65ca934aa16809f898cdb59727372a7891a7be10f6d65c8fce29adfc9e66fadb59720792a5e62e7756c75d65c7bd62944cb9d4467d75971ddc0a43e1e72cc7b5d65c7338a8d98d9c21d6d75971bd04a28a1e6e42375d65c64d9a877a99aff44d749715e4ea145fe69b7eb5d25c4924a82c4399dcb1d74970e506a0204a652da35d25c304427e51698ba1fd74970a2249f0e5260a35b4d25c1edfa7af7c97978d) (by decide+kernel)

private theorem _DSC:WideCovered band27 10492631 11385263:=PRB band27 Z1.f567 10492631 11385263 (WB 1305879435352 16 0x77ccbc32de72237f56dcd7bbe65dfd64386b8eab25c71df12ef6be5be9dad56e914ef89775532dde740aa51f877c4bb51a96e89be5497b33be25d6a533756be2a03353df32e2d74dca52b94dd484ef89727e5ada7a35a5c7b06fbcb9fb60588d6a52528f37da5cf1ceac06702904f55bed2e72c2d5e2f91470518df6973630cae1474a2f1436db4b996e2568788512ffcb6da5cc2a8ab01b82873ac1b6d2e5f739562891427acedb6972ed88aa231ca0ac1f) (by decide+kernel)

private theorem _DSD:WideCovered band27 11385264 12575441:=PRB band27 Z1.f564 11385264 12575441 (WB 206367841304 16 0xffc971ab6c4d4ca9bfe2d1ffc9714fbc4b3cdabec03effb970d163497022bd9dacfbb97052df47abb0bc7b1afbb96fe7d345ec37bb5888fbb96f9bd0446381ba35f6fbb96f32bf42fd39b91364f7a96ecef241bb92b7f0d2f7a96e8251407263b6ce40f7a96e496f3f3c3eb5abaef7a96def733e2a01b4891bf3a96d91863d1b6cb36689f3996d4a023c0ea6b243f8f3996d2b753b11dcb12165f3996cdb673a4a6daffed3f3996c8522398a7caedc40) (by decide+kernel)

private theorem _DSE:WideCovered band27 12575442 13542460:=PRB band27 Z1.f564 12575442 13542460 (WB 240727579672 13 0x10fd97d07287c1a2dcea43c87ecbdcb20bb230266c0d542f65e8ed11c3431b317c6217b2f262c0d7db6b96790d0bd9782fb867ece3ca19f483ecbb9647b1f451647bb141f65d8cc918047a31f53420fb2eb0d74b96c1f8d647b07d974bf0459abc5c58fab81ecb9fe35ab5e34e2368d40f25cdc2354fb6a30d2a1e0792e5a560a327c1844feaffc97245ab4f88e2c10562) (by decide+kernel)
theorem covered27:WideCovered band27 (AX band27) (tail band27):=(_Q1 band27 8781749 9358241 13542460 _DRZ (_Q1 band27 9358242 9897540 13542460 _DSA (_Q1 band27 9897541 10492630 13542460 _DSB (_Q1 band27 10492631 11385263 13542460 _DSC (_Q1 band27 11385264 12575441 13542460 _DSD _DSE)))))
def band28:Band:=⟨8,68,3468,4337,21427213631395185⟩

private theorem _DSF:WideCovered band28 8912820 9401424:=PRB band28 Z1.f568 8912820 9401424 (WB 1306953278584 16 0xe7ce605b5430979c92c7ba2872e530373a9048ba1f23caba3972981b019424710691dc2ffc994c0da1d211fde938e9817e5ca606a3a70904855c7275772e5303342e0486bbce3815198b1981d3ef8219b2a51b77bac58cc0e921a10c78d28d727562c660742150860ce546948631633039d66842ef20a337e918b1981ccca4216c215192c76c584c0e563c10b07ba8c4cd35ebe35685b759a15ecc601b52f5f19dfe8e9f59ac022dc26572e8c5cecec61ef3511495eeb97461ceb921e289e0892555) (by decide+kernel)

private theorem _DSG:WideCovered band28 9401425 9814859:=PRB band28 Z1.f569 9401425 9814859 (WB 1305879402584 16 0x6bacce25dca07d2495c34bebaccc58c6a3034795307be9a4ce928e9bfcf2949daae9a4cdac969d1ac6940ad86794cf8fee8ff1219378076794cf6ad88fbf1592e536679ccf642e9270e0925265679ccf428c9246509208fd679ccf227c922de891bf94679ccf046a92365491762c679ccee57e9232c4912cc3679ccec45e922dd490e35b679cce9f709231449099f3679cce75c4923f1490508b679cce3c16926dac900721679ccda338935ba08fbdb9) (by decide+kernel)

private theorem _DSH:WideCovered band28 9814860 10416218:=PRB band28 Z1.f479 9814860 10416218 (WB 206367807512 16 0xdb6992ad62a50bde7bc16b6da64a14029172f9e5d8adb5992500ea3bb36772ae76d664851528c1479d37e8db5991d35ea2508672945f6d6646a922877909c1245d759918e3ca130966dfdd35d6645c392821299aeca3d7599149c2a02df669674b5d66449a4a7e37b99c702d75991000c9ef1c664d0c75d66430b1a7b4a098a160d759908afa9e5596603a3b5d6640fe9a77e32977bbed7598fb7ac9e7f965ba3b75d663d03ea7b58f96561c) (by decide+kernel)

private theorem _DSI:WideCovered band28 10416219 11092748:=PRB band28 Z1.f570 10416219 11092748 (WB 206367807544 16 0xf3999296d6e80409528619e733272ebdba33a6a075a78de652e00acb43d537be471bcca405f58d706a664f7e379944760b088b14ba44dbef328230d5f284294fd577de64ffa82b9a445256426fbcc9f7a5569c42a419b2df7993dc52ac4401470dc3bed327532956a9128bd0477da64dd252a99125130a06fb4c9a16b54d310a1ce6fdf69930824a8b49142773db6d325c6bd4f812a82a33b6da64b3bb29c130500afe6db4c95eb95305b49f832b) (by decide+kernel)

private theorem _DSJ:WideCovered band28 11092749 12295467:=PRB band28 Z1.f571 11092749 12295467 (WB 206367841336 16 0xfbb990139844d0fbddce95fddcc7cfb221b13bee9de27eee63da77d0749e372a3d1f7731e16ba81671bb82c45f7b98ea08b3f7217db8351fbd4c71e679f28916d78407dea638a204f502976976bfef531b9b6e787e5db395bdf7a98d779b3b7b92d9380df9d4c68d4b1d6229ec529e7cea63383e8e757476049afe7331986a67269cfaeff35f3998c7783388e7fd6ecc9f9ccc60d771c2382eb2cfc7ce662e82ace00c71571c9fe7331613fa707e8caa68ad) (by decide+kernel)

private theorem _DSK:WideCovered band28 12295468 13498186:=PRB band28 Z1.f481 12295468 13498186 (WB 240727579672 16 0x87f4cdd3e3b968cee6fba543fa669b2a1b832cf33469e17d3325224d24e7197580d0be998402564ea1cca866485f4cba5b2b0a12fe4b06141fa6597c5177062f20ec7e0fb32b07a6b51a058e2afd07d994e16d576942c5efdc83ecca18a62a6fa0e2651d40f664e122149a7f30e926207b325f3be9f7d8584fdef03d99271f24dc463c159557fe4c8eef325da946019d93ff264537a5270312fc3841ff932207348ff0737bd0deffc99085ac4645d5bcc2cc) (by decide+kernel)

private theorem _DSL:WideCovered band28 13498187 13723695:=PRB band28 Z1.f481 13498187 13723695 (WB 240727613464 3 0x113e990275da17595745a0be1fd31e954a3f8826e82146c3fa639b5407845cfcf1ceb) (by decide+kernel)
theorem covered28:WideCovered band28 (AX band28) (tail band28):=(_Q1 band28 8912820 9401424 13723695 _DSF (_Q1 band28 9401425 9814859 13723695 _DSG (_Q1 band28 9814860 10416218 13723695 _DSH (_Q1 band28 10416219 11092748 13723695 _DSI (_Q1 band28 11092749 12295467 13723695 _DSJ (_Q1 band28 12295468 13498186 13723695 _DSK _DSL))))))
def band29:Band:=⟨8,69,3420,4305,24557676242331921⟩

private theorem _DSM:WideCovered band29 9043891 9423659:=PRB band29 Z1.f572 9043891 9423659 (WB 206367908984 16 0xcb19a1e2f6821a980f1f9657963343c1f60433da7e3e03ff1c66877b8a086524fc79b69638cd0ee54810c56278eeca6c719a1daaac217a5ef1d44f39e7360c1f0aec575ba3961373ce6b9d9725a7118ac70710e79cd61aff6b0be4f48dc3f5cf39a794d012204a471af39196536706072d3f776a34be732ca6cbc5e1598e1994672b7e594d989f3eb8a47b28c9b43cb29b2ae8b1745987518a22d7df1ad39f72d6350c6301baafbe343fb834451e0845de5edd74651165652484888b2864) (by decide+kernel)

private theorem _DSN:WideCovered band29 9423660 9727474:=PRB band29 Z1.f573 9423660 9727474 (WB 1306953144440 16 0x68d26fe28749af39651b7c9a349bf4e7126ab2d9423c668d26fc59b4995c964f6665a349bece8926605d938f6d68d26f9f68499fab64d1501a349be21a126b62592fb1368d26f6f1149bc1564ac39da349bd50292717359266bb68d26f300b49ef81648723b9f39bc450927982491d262e7ce6eed7649e456e4620d79f39bb83e925b552913e09e7ce6e9cd549d1c2a43cf739b39bb48f122bc9990a9b0e7ce6e816a4937886417e119329be4a090dd520901558) (by decide+kernel)

private theorem _DSO:WideCovered band29 9727475 10297127:=PRB band29 Z1.f574 9727475 10297127 (WB 1306953177176 16 0x6cda6c8aa52857cb2747c9db369b20338a0e3e89c8ace6cda6c7688a80ee826fd9d5b369b18ede9feab09b621c6cd66c4f0427f21926b370db359b0ee969f6d049a396a6cd66c28d4a7e1ac2669449b359b053229f68409910b96cd66bf61b27fdb9261f181b369aeb918a1841097e807ead66bba24a7ce2be5d4ebfab59ae825e9de91e96bf56ebd66b418727fca4a58abf5a339b0155490a6959596a468d26bfe5824e099254092da349afe04a936dc894b81f) (by decide+kernel)

private theorem _DSP:WideCovered band29 10297128 10904757:=PRB band29 Z1.f483 10297128 10904757 (WB 206367807512 16 0xe379b4c206ae99c29992d78de6d23b22b6e99a5d05ce379b45346aca95694f00f8de6d06c6aaf2b7a4a7aadf79b3e482aaeda6904d477de6cf42a2a7571a37ef8df79b3bbf6a8f62e8baa837de6ceaa629f507a25647df79b38652a7116a8707bb7da6cd2eba98e14a12d95df69b313aaa596f68264f77da6cb5dfa93ed0a004e4df69b2a1f8a425c67dc22f6da6ca0ff28e4a39edc32db69b268f2a2bd9a791f676da6c91d9288d3a9db380) (by decide+kernel)

private theorem _DSQ:WideCovered band29 10904758 11930132:=PRB band29 Z1.f575 10904758 11930132 (WB 206367807576 16 0xfbb9bcf4bcf6183ab60a14f7b9bc35a0f2f0aab4e163f7b9bb9a2aef2d32b3b8b1f7a9bb682eeb7e22b29000f7a9bac314e8db1ab1674ef7a9b9f890e6a8f6b03e9cf7a9b90b78e4e3c2af15eaf7a9b7fccee45c5caded38f7a9b701c6e490a4acc486f7a9b51490e774e4ab9bd5f7a9b2810ae86ad1aa7323e789b57b46b47ab0a94a72e389b53d14b342d8a8b619e389b513d0b22b50a821c0e389b50170b0d958a78d67e389b4efdcafbb34a6f90e) (by decide+kernel)

private theorem _DSR:WideCovered band29 11930133 13145392:=PRB band29 Z1.f486 11930133 13145392 (WB 240727579672 16 0x85f4db3e07ada49be44a9841fa6d6db3d6220d31db1fe0fd369c5f8ab26618c879b07e9b45a5552e14bc51b1c83ecd9d7962843a961f93540f66cc17ad38f58f0b26e207b365013297fde383420d03d9b20b334a15d8c0785481ecd8c0b1a425fbdfa7d13ff26c415751b1ebef89bc5ff936166e48a176979fc7effc9b04c8a439daebbd58e7fe4d7eca3a120925d566e3ef26bd891503a4dae610a9f7735e600a7f25c970b6f0fbb9aedc3b3e7c76b732c6) (by decide+kernel)

private theorem _DSS:WideCovered band29 13145393 13904930:=PRB band29 Z1.f486 13145393 13904930 (WB 240727613464 10 0x22fd36441f548c84b6a161144fe6c401ca88ee40d3037089fcd8018c1020c89a3b57d13f9af467c9ebc5e342c8361ff35d02df3a905be7c4adc3fe6b712566f93f8ce60aa87fcd69c1a4d552a19a6ff10ff9aca58899994af303d1a17d3583236312b8de5734a42fa6aeb6085e7785c9bde2) (by decide+kernel)
theorem covered29:WideCovered band29 (AX band29) (tail band29):=(_Q1 band29 9043891 9423659 13904930 _DSM (_Q1 band29 9423660 9727474 13904930 _DSN (_Q1 band29 9727475 10297127 13904930 _DSO (_Q1 band29 10297128 10904757 13904930 _DSP (_Q1 band29 10904758 11930132 13904930 _DSQ (_Q1 band29 11930133 13145392 13904930 _DSR _DSS))))))
def band30:Band:=⟨8,70,3374,4272,24569753719017764⟩

private theorem _DTK:WideCovered band30 9174962 9481911:=PRB band30 Z1.f576 9174962 9481911 (WB 1306953278584 16 0xe7ce706bc2f0908a73c8575bb265383d99a042c845a418f1d9329c1eaf4c21560bd2031aec994e0f466210a738e8fcde764ca7079b1d085032347c17b3263383c9198426be1a3ce0199b39d0918d14ba63ab1dda2acd9ce862066afc3f5d8ea22566ce742ea455d78382472b9a336739d57ecad04706e3831119b39cca1e0d6903a451b82a6c994ea183c0b3bb1198d766364ca74edcf35936920c695b932653a6a20cac93bca63382099329d21f76556c1371192b22c994e8ea60eadd6b688c4aa1) (by decide+kernel)

private theorem _DTL:WideCovered band30 9481912 9788861:=PRB band30 Z1.f577 9481912 9788861 (WB 1306953177176 16 0x68d274167da486cea5576f5a349d032c691ea469512cd68d274057ea47984a531f75a349cffb4091c552947ced68d273f68da473b8a50c7f1a349cfba3291b9c693e70c68d273e5c1a46ac4a4e706da349cf69b491d1be93512b68d273cf3f2475e0a4c18e9a349cee13a925f4292bb4a68d2738f77a4d4f1a49c16ba749cc5fea96bdfa92256ae7ce739fbe24439964769e79f39ce2b169157e1918f89e6ce738f39a3e86d24512639f39cde3ca8ff92490f9a8) (by decide+kernel)

private theorem _DTM:WideCovered band30 9788862 10402762:=PRB band30 Z1.f578 9788862 10402762 (WB 1305879435352 16 0x6fb4e95c2f50d6f7cf5de536da74a5622846dce7897a9b6d3a4e98140a7173b2012db69d24e649fb79f9cfa286db4e910bb4f9d5dce3223b6da747b5c27b357e6f399db6d3a35d893cecdf36710cdb69d15f449e41979aa2a56db4e884484eec71cd066236da742d13277e84e65db91b6d3a016753da21f31c207db69cdb3cca3137f984b226db4e7aceb4eefaf4bdaa0f5d673c9a726f35565c7d81a673a103291f48692d12fed339d05e7e8f4d7c95f39e) (by decide+kernel)

private theorem _DTN:WideCovered band30 10402763 11016663:=PRB band30 Z1.f483 10402763 11016663 (WB 206367807512 16 0xe389d55dd6b00a9ea0675f8e2755242abba09a783f7e389d5365aad86e29bb85b8e27544002b20bba65835e379d4d9deab9bb69709538de75285baaad72a52c74e379d46626a9d086925a4f7de7509f52a3329a400b2df79d41174a7cb468dab477de74febea9b8a3a2d4f1df79d3e518a5f7ee88fc437de74f2d1294506a1a92fdf69d3939ea469ce844d3b7da74d455a8e2bda07d6ddf69d310eaa2e69a7f9e337da74b63ba891da9f51ab) (by decide+kernel)

private theorem _DTO:WideCovered band30 11016664 12167726:=PRB band30 Z1.f579 11016664 12167726 (WB 206367808600 16 0xfbc9df8d8a816d1bdcd5177de4ef658f3f4a34ee1f9b3eee779b519f1a2c76ea557f773bb6158f55e63b626e9fbb9dccbaa7894b7da7d947bdcedf8983b847becf3d9bdee76eced9d40e77654749ef53b6b1d4e78037b177e3f7a9da8ab472b20c5826117bd4ecd84d3922402bc8183dea7628241c97fe95be93fef53ade03ce4ef0cacc8ddf7a9d4b76a73cc5d55ce8e7bd4e92cd839a6726a9c56b9e27573159649371528b33c713ab1e4cb12afca8afb8) (by decide+kernel)

private theorem _DTP:WideCovered band30 12167727 13395528:=PRB band30 Z1.f486 12167727 13395528 (WB 240727579672 16 0x87fced13a8337287e6332442fe763f2e98ac2632cea1a17f3afdedcbde81b941d8b0bf9d725c85b5649c8e30385f4eb27fd2c34d6e3dba141fa755fe555664d31a2e020fd3a9bb1ca52d278abf7d07e9d435de505ccec433fc81ece9c85e271ac5e1841dc0f674b6cd12f5e630771e607b3a508e893cf9f81617103d9d1f5604817fabf84f67fece8b51923321e5f2c9abff2743d431133456f4b5cdff93a14c94864d13780362ffc9d037ed41e9edbad5ef) (by decide+kernel)

private theorem _DTQ:WideCovered band30 13395529 14086165:=PRB band30 Z1.f580 13395529 14086165 (WB 240761168984 9 0x4c7d39d47363411246d6f0159ae6725f5b195eab03ab88a91604e97b09c93f28d352624a2c09d1ccf21169d0469b668c4813a150da20b35b4d2410f890273f640a3dfa1b1a22a9d1204e786f5c76206433fa6321c09ce40238e07294675ee5c37f39b53171ac8730cd9209) (by decide+kernel)
theorem covered30:WideCovered band30 (AX band30) (tail band30):=(_Q1 band30 9174962 9481911 14086165 _DTK (_Q1 band30 9481912 9788861 14086165 _DTL (_Q1 band30 9788862 10402762 14086165 _DTM (_Q1 band30 10402763 11016663 14086165 _DTN (_Q1 band30 11016664 12167726 14086165 _DTO (_Q1 band30 12167727 13395528 14086165 _DTP _DTQ))))))
def band31:Band:=⟨8,71,3329,4237,24518427604801520⟩

private theorem _DTR:WideCovered band31 9306033 9616118:=PRB band31 Z1.f581 9306033 9616118 (WB 1306953278584 16 0x68d278702c5091012f495d7b74e93c32996849bef7a49bd099329e1f92cc216538b24471cc994f0fb89210ab90591d7da64ca787d37c085248ec8c612b2653c3e4b0042805d24501c59b39ef610bd61b7db721e978cd9cf7160ecb82e08390a90866ce7afd2f86065b81c82ea9b3673da7f7127bc8e0a40467d9b39e23b37f8d7b9551f8bd4c994f89a8268c562b98f7a3664ca7cba5505939674479740b2653e39264ab831fe23b8b359329f09e7cd55585611d2e30c994f7acd10a8988088e4b64) (by decide+kernel)

private theorem _DTS:WideCovered band31 9616119 9926203:=PRB band31 Z1.f582 9616119 9926203 (WB 1306953177208 16 0x6ad67c308224bd46d2eec76d5acf85380496a17a5caa1dab59f089b692b8174b6f69b56b3e0d87125203596931f6ad67c1258a49fd0b2c8ed4d5acf81153493b41657eedba359eff5be9284224ad800f4e93df81d1254a2c95644de9d27be1b224b12a92a3131d3a4f7a12e497c8b2533393a749eef77a9328a9ca409874e93dd27292736eb94357ce9d27b8520a51123727d38fd3a4f6ee4949cb28a4e784fa749edc3fe931904c9a92fb4693dd671d1fd0389306ab) (by decide+kernel)

private theorem _DTT:WideCovered band31 9926204 10546374:=PRB band31 Z1.f583 9926204 10546374 (WB 1305879435416 16 0x6fbcf9bcf9513e63541d98cdf79f35ab8a1b07ea815579bef3e66bb1423744cfdefab7da7cbb9928270e99f268c6fb4f94de65005db13d1e46df69f250849fb7d2277def1bed3e432793ef4c3ceb029b7da7c76a7a7ceb979cc8ea6fb4f8caa74f77acd386302df69f12ad69f57d5a6e6865bed3e166f53f1542cd815876da7c04fb28006f49a6b47edbcf79315508236733a7bddb69ee5154a0a818a64f1d7b6d3dc4b613df478cc5286b4d27c39eea3eeaf0980da4) (by decide+kernel)

private theorem _DTU:WideCovered band31 10546375 11166545:=PRB band31 Z1.f584 10546375 11166545 (WB 206367807640 16 0xe799f64a92b1a7462a98d479e67d88e32c17d77a9cbe9e789f5e87caf5101ea4d2039e27d6bd72b98e26a89d18e789f56f80ad557daa016bf8e27d4b1f2b0c555a76e47e389f514c2ab1f0569b5b7b8e27d3f612a8c0a4a63f75e389f4e796a9181d296a0338e27d2f70aa035f3a510a4e379f48636a75af0a91e4ef8de7d11c129a2732a3e1d2e379f400c8a5a3ec68d29ab8de7cf4c22935291a2b301df79f3b486a42fd02886e637de7ce59928d9470a1842f) (by decide+kernel)

private theorem _DTV:WideCovered band31 11166546 12329366:=PRB band31 Z1.f585 11166546 12329366 (WB 206367841432 16 0xffd9f083fa42424efbc2196ffc9f0582a40e898ebaf2c4ffc9efe6493fbd96db9c3f3ffc9ef7a923ec7b8cb89522fbc9eef9273d9a8dbb76651fbc9eed60e3cba0aab6377ffbb9ee95b13bbb249b508adfbb9ee34693b359f8b3d9dbfbb9edb4f83a83f87b2ab0bfbb9ed31393a451d6b17c39f7b9ecca6b39e1c15b04d68fbb9ec13e63a60c04af1e96fbb9ea8de83bda1b3adefc6f7b9ea80413941932acc0f4e799eb3b862d09151ab9223e799eb30302cbe600aafaba) (by decide+kernel)

private theorem _DTW:WideCovered band31 12329367 13569708:=PRB band31 Z1.f586 12329367 13569708 (WB 240761134232 16 0x89027f152f1b3a553f3c3ab21c09fb0914685aedecddfdb87027e7c9558eae87732c42a1bf9f8ef97602988ccb823884fe7df7d3971e326f294d9e13f9f6ed8059442dac9249684fe7d90b61588ce671fd71213f9f581cd539fdb8c6c6f282fa7d2c281439bc5f1660860be9f435bf4e890d6c4694f82fa7ce529d31c8ad70ce9fe03e9f2f6d24a805a4c20bad80f67c970ed22a560f03737203d9f2035946a3762bfae0a80f67c61f2914e5206f9fce5fbd9f0fd7c43a67a0bd5067) (by decide+kernel)

private theorem _DTX:WideCovered band31 13569709 14267400:=PRB band31 Z1.f587 13569709 14267400 (WB 240761169048 9 0x135fcfc9da4cf911978d9b4089cee7ba130fce36a63ec429bc6833eacdcd28c5be9b5d59962c19f3edc4930abf6bac4f29160cf9400808de91e4d4f8c28b067c62e544305cb1e9e4f944833e118a81fb6740b4a6c822409ef933b0efafc63a2d89f1204f77420c7233320d03d7d) (by decide+kernel)
theorem covered31:WideCovered band31 (AX band31) (tail band31):=(_Q1 band31 9306033 9616118 14267400 _DTR (_Q1 band31 9616119 9926203 14267400 _DTS (_Q1 band31 9926204 10546374 14267400 _DTT (_Q1 band31 10546375 11166545 14267400 _DTU (_Q1 band31 11166546 12329366 14267400 _DTV (_Q1 band31 12329367 13569708 14267400 _DTW _DTX))))))
end
end AY

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AY
open AI AP AN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def band32:Band:=⟨8,72,3285,4172,24536063114686191⟩

private theorem _DTY:WideCovered band32 9437104 9750324:=PRB band32 Z1.f2177 9437104 9750324 (WB 1306953278616 16 0xe9d280748f5090151aa531cd3a74a01c767c241c9b9947abc66ce807d99a085a80a250b9119b3a01f2ed02160cf793e1cc66ce807bcc0085486de4e554d9b3a01ed23c21472569348db66ce83e6e63458141d64bf189a33a133384d5c7a26492afeb68ce849e17155ad7b92498dc9a33a11ea97d55a1c749216fa68ce845f414564ac5ce472a05932a0df1734e072d52917e0964ca8361b1a364b920a44c6419b2a14352195af15e190e51864ca84dfa5754b3c20642627d932a12a3c3d489a160904c27) (by decide+kernel)

private theorem _DTZ:WideCovered band32 9750325 10063544:=PRB band32 Z1.f2178 9750325 10063544 (WB 1306953177240 16 0x6ad6842c0724e2429998eb86ad6842493a4db8299942406ad6841d1da4d16a898f5c86ad684143524cd09898a9516ad6840ae2a4c7337985cd86ad68401cd24b9fe79810606ad683f650a4b703697c3e76ad683e90ca4b73b597776f6ad683d77a24c4595972af66ad683c62ea4cfef496de7e6ad683af5ba4efe24969206ead68394e6a51487396458eebd6837675253c56395f915ebd6833d33a59f51295ac9eebd683319da583a61956025ebd6833a7025398f09513ad) (by decide+kernel)

private theorem _DUA:WideCovered band32 10063545 10689986:=PRB band32 Z1.f2179 10063545 10689986 (WB 1305879435416 16 0x71bd09baf151d88df463b84e37a132e36a2fdf3a8a1349c6f425c96944f47ed0f5f0b8de84aa31a88081ca152f171bd0940b950a3bd7417400e37a125358a0c4a2a808441bef424358140ec64cfc40fb7de8475c82810f989eef2e6fbd08c26b50163cf3cac7cdf7a112cee9fdb15a76f539bef421377540aa92ce922ef7de83eed2a85e9949c8b6cefbd0743945166b0737e4f7df7a0e8b06a0e6bca6d662dbef41f298d39df30cd604d35d68439cd23fdad09a27a9) (by decide+kernel)

private theorem _DUB:WideCovered band32 10689987 11316428:=PRB band32 Z1.f2180 10689987 11316428 (WB 206367807640 16 0xeb9a164c1eb3a187eb2b333ae68583f82ca2ddeac13dceb9a15ca9eb13f476adebaf9e68562522c09dacaae1fae79a156664af0efaea9242b9e6855421ab6dc7aa9b01ae79a153b30ac97826a45ca79e68543bbaae9248a87e38e78a14d2a4aab641e9f951f9e2852572aa77756a74c58e78a144e1ca8cc9569acd9f8e28507cf29fd794a61a76e38a140400a72110e9606178e284fae22981f32a4e894e38a13d088a531486913e938e284ed532916d20a3b6b3) (by decide+kernel)

private theorem _DUC:WideCovered band32 11316429 12491006:=PRB band32 Z1.f2181 11316429 12491006 (WB 240727579800 16 0x81ed08800121f4667df4c7f40f684244350af563af59c7207b4201e8882bd51b786a76ffda0f97c6404a8acbb035a7fed07b1c11f7b58ddce8bcbff283c6984f8143eae27e61ff941d4cb67a2a7736edb6cffca0e38823c7e2a8b63bd47de506e0711dd98ebda84fa3ef28362b34ebf57dacf6049f7941a51ec75d31eb654c64fbca0cab343abc474b174507de5059c8d1e07b81d821383ef2826240cf06404abc4239d75416a8ac5aff3a35bbd5aebaa0b43432d2e2a0ad45bd) (by decide+kernel)

private theorem _DUD:WideCovered band32 12491007 13743889:=PRB band32 Z1.f2182 12491007 13743889 (WB 240761134232 16 0x89068779441d0ff1ff46dc46241a1c450b6e671fed08530890686cdc2da7028773d4d3e240a19f516654839cce216d87028636a3d85b896f33be361c0a17f67e5d6b81acbbdab870285c227168ce8272a2f2a13fa1622d85722738c959e884fe8553be95183c5f20a01e13fa14c4cc51a6a06c6f62684fe85049853d71f171711160bea13606d4d20124c4926482fa84bb1292b2abcf0d820e0bea1268f44925682c22ea182fa8475c251da7b8703f30203ea113fe045acc90bfcade) (by decide+kernel)

private theorem _DUE:WideCovered band32 13743890 14448635:=PRB band32 Z1.f2183 13743890 14448635 (WB 240761201816 9 0x2740a119d31961d7b88dc77fb9d0283d6897574acbdf6d186a3c2a0bd43c0b6452d6da14388d0a82b85b12a0ca297638962342a0a251bc9c42364d7b0768d0a825cee02482b98f59fa5a2c1a08d2f4888d15f2d54cb48b0682138be20436f07506b4e2c1a07e22047a288c0d2e8f2) (by decide+kernel)
theorem covered32:WideCovered band32 (AX band32) (tail band32):=(_Q1 band32 9437104 9750324 14448635 _DTY (_Q1 band32 9750325 10063544 14448635 _DTZ (_Q1 band32 10063545 10689986 14448635 _DUA (_Q1 band32 10689987 11316428 14448635 _DUB (_Q1 band32 11316429 12491006 14448635 _DUC (_Q1 band32 12491007 13743889 14448635 _DUD _DUE))))))
def band33:Band:=⟨8,73,3242,3923,23530484371342618⟩

private theorem _DUF:WideCovered band33 9568175 9884530:=PRB band33 Z1.f2184 9568175 9884530 (WB 1306953245848 16 0xeada88a67d4126af364b69b975eb4454dd40913d82e5a18dbaf5a228a66048db7352c71f5d7ad112b2bc24c840995ebbf68d288bfae810b8f0c4acf413467445f80b08583c1e554519a34a3fed8baaa9be6d2a0812d1a51f468d948fb63694b6cd68d28f7cb1aa29119aca34c83469479b6c34f0c9912507151a34a3c0dee26d541a9279e30cd9d1d5eb05162c3439381dc66ce8e6dd868661271499a4fb367471b177413eff4a4b9d8d9b2a37a5181f38092325344cc9951b62efcf207440924cea) (by decide+kernel)

private theorem _DUG:WideCovered band33 9884531 10200886:=PRB band33 Z1.f2185 9884531 10200886 (WB 1305879402648 16 0x6db51d15da93fe0726e9cd9b6d47414ca4ecbfc9b59fa6db51ceec4938956e6c32f9b6d473342a4d3afa9abf826db51ca8ae933fb2669c915b6d47204c24cdeb89a250a6db51c53e6931fce2675f35b6d470cae24c9c97998a916db51c1596930c4da64f551b6d46fb8a24c9f8598f0186db51bc09a9352f92628b71b6d46e413a4dc3949855a06db51ae5f2949c1ce602191b6d4671bea5a323297bb286db51af1c69363e865db7afaed46b3e024b32109720af) (by decide+kernel)

private theorem _DUH:WideCovered band33 10200887 10833598:=PRB band33 Z1.f2186 10200887 10833598 (WB 1305879402648 16 0x73c51f12f0a5220be953af9cf147b4e9291bb4ea4b44671c51ebb9ca3a3cf6906739c7147a870a8beccca37f5571c51e8078a29182e8b9371c714799402875f9aa24a6571c51e407ea1504e686bfb1c71478761a829ab8a1157371c51de25ca0519de81ebe9c7147638ea81d5569fe08371c51d27caa058b967d1829c71471f6ea83d8349eab9171c51b6160a2a7c0e784467c714627c829d1e029d76a0efbd1bd1e69dc490673709fbef46ac5027ed0309c41ae) (by decide+kernel)

private theorem _DUI:WideCovered band33 10833599 11466310:=PRB band33 Z1.f2187 10833599 11466310 (WB 206367807640 16 0xefaa317578b5d16bebbd91baea8c4fecad234beae5bcfebaa310750b331036b7055baea8c3ef3ac8211cad26ddebaa30f3b6b09676eb23193aea8c346eabe29eaabf1edeb9a30a208ae85ea6ad5dd3ae68c1b8eab5b488aabcfbeb9a303808ac5639ea88a0f9e68c00052ad3406a9880be79a2feaf8aa6ea16a3b64b9e68bf7f2aa53724a8531ae79a2fd460a84310e9ee2879e68bec9829d2d92a71e28e78a2f8098a6895069a0ebf9e28bd3bb297cab0a5e937) (by decide+kernel)

private theorem _DUJ:WideCovered band33 11466311 12652645:=PRB band33 Z1.f2188 11466311 12652645 (WB 1340239174808 16 0x41fa8ecf42a318f6fe08832a0fd474c5e5128527aff6dd103ea398146862fd5b7d4d0881f51c892c41c162cbd719240f68e25f3203e365de1e51207b46fe7dcfe955aaec1ec0ffda3728d47d3321373a57e7fed1b2c5a3db7bd8b89dcd3ff68d8b319e70a2bdbb46e9ff946bc664f06621ad8cfb0ffca351b3a7751e2b69fdf67fe51a25403bdd8c4b3ca0a3ff28cbc1f1df85a1d94a8cdffb4506325052914ac580a0efaa31dd865c3538360567077d518d5a22dca110af90bf) (by decide+kernel)

private theorem _DUK:WideCovered band33 12652646 13918070:=PRB band33 Z1.f2189 12652646 13918070 (WB 240761134232 16 0x8b0a8e37bc9f1fdb7f517dda2c2a37a3ea75f0d4ed32a848b068d9d60dc164b3747d652241a356a6e6b978bcd0c0a389068d153199a996ef3e2eca241a339913626176ace56c189028cb32717b46ba734873e1c0a31fa385b2bd28cbecde87028c5ec396053f1f2adfba1c0a30d399553b2e6c982fc85028c0d3694a5bb9721383213fa2f95fd4fff104c7191a84fe8bd04e136848cf1790aa13fa2ebd6e4b858f2c4af3982fe8b90789268fb870de91e0bea2def90479b860c24556) (by decide+kernel)

private theorem _DUL:WideCovered band33 13918071 14629870:=PRB band33 Z1.f2190 13918071 14629870 (WB 240761169048 9 0x13a251b7d1492ac6b48df3bee9d128d8d0568a5bcb3ef037ec78746a08ae3414b31b7348323c3a32fb291798e7cbb73a371e1d18c7f58ae05024da682a8f0a8c0d6e850926f1ec999cc68545e0b8325789bcb5ff922342a2e1ad6918504e3ad92b11a15169e31083fc930d59466) (by decide+kernel)
theorem covered33:WideCovered band33 (AX band33) (tail band33):=(_Q1 band33 9568175 9884530 14629870 _DUF (_Q1 band33 9884531 10200886 14629870 _DUG (_Q1 band33 10200887 10833598 14629870 _DUH (_Q1 band33 10833599 11466310 14629870 _DUI (_Q1 band33 11466311 12652645 14629870 _DUJ (_Q1 band33 12652646 13918070 14629870 _DUK _DUL))))))
def band34:Band:=⟨9,49,4403,4781,8278075124780465⟩

private theorem _DUM:WideCovered band34 6422470 9199279:=PRB band34 Z1.f2191 6422470 9199279 (WB 206366693528 16 0xcaceb6deb723417f18bd5f8d9d7ba32d4e917a2da0ab1b3ae8b45aabe6ec538d2e367599bdb5f005c897b1fc2ceba3cc6438b371109336dbd774d6bad742a1e3852db7aec58973d134c38968db6f5d8882e3cd0886978fb6cebb59a5c0634f0c38996d9d75e22b763dda16842adb3ae9f016d48b2c292e3db675d00d2d7970484aa84b6ceb97f95a92327085e84083d00cc601f060a0ecffc107a00fc40235b0c15ebd020f4015c002c05080d06f) (by decide+kernel)

private theorem _DUN:WideCovered band34 9199280 10209028:=PRB band34 Z1.f2192 9199280 10209028 (WB 206366727320 16 0xd2deaa982a09c617cde382696754ec49018fbfa6b41fb4b3aa46c67f3e9db33b3f39d9d508ff3eca8dc98e374cecea763b1ef93edcbf677e76753c314f4f93ea5bd9a73afa9b562793b8b32bffc99d7d4c2d83bffbf895095fcabea54fa1dbbf73ca096d655f522e74eb7fa1a4c71572b3a90594749124b244b9f959d487c239e2714912f4acacea37699cc9eb9c81c62656751420ce5705ca3d08ff2b3a8560672d8b631c9775959d3efec39b09508d5534) (by decide+kernel)

private theorem _DUO:WideCovered band34 10209029 10461465:=PRB band34 Z1.f2193 10209029 10461465 (WB 206366727256 4 0xd6dead89f22b103f3f4233adbd5936a443de7a7aaa4f4b7aaeddc8666f4ceda07696f556a6d08de349cbd89) (by decide+kernel)
theorem covered34:WideCovered band34 (AX band34) (tail band34):=(_Q1 band34 6422470 9199279 10461465 _DUM (_Q1 band34 9199280 10209028 10461465 _DUN _DUO))
def band35:Band:=⟨9,50,4323,4757,8462320411597642⟩

private theorem _DUP:WideCovered band35 6553541 9364838:=PRB band35 Z1.f2194 6553541 9364838 (WB 206366726296 16 0xcededee7539a23cf8ee566ceded3b9dbab3a0e8debd1c6dee5565b47b8ed8cf23cc6dee4401b476e9c8bf8a7c6deda6deb5daf2b8aff11baeee3072aec35ba8a057cbadee326c2e820e98988b1badee2e852e538a8890be7badee2a182e1d627888f1cbadee2573ade66d6881252badee20ee2db6635879587b6dee1bbdad7d7248718bdb6dee169bad4bfe3869bf2041ec03ad807af62861f28041ec02448045fd1852593043ec018f802b810833268) (by decide+kernel)

private theorem _DUQ:WideCovered band35 9364839 10387127:=PRB band35 Z1.f2195 9364839 10387127 (WB 206366727320 16 0xd6def2706a115a3fcf3f5beb6f78bcf104f95ba76148b4b7bc1ef080aa9fb39171ba5bddedaf3f697dc9b91f8d2deef6439f49375cd4c31e967774d70f7b7baa667b3b4b3bb6e407a798b3314a739d9dd98763c8cdb897aba4ceceebb119dee5c3cb5907e76f7602ccec4051a56e1eb3b7bacdec752b98b297dcb9dbdd4a273a249a493c550cedee95539cebb81c965dd676f7404c4e62114a4748972b7b991ec72b14a321b12195bdc715b3967d008fdefb) (by decide+kernel)

private theorem _DUR:WideCovered band35 10387128 10642700:=PRB band35 Z1.f2196 10387128 10642700 (WB 206366727256 4 0xdaeef60a7a341a3744ca19addde9fd54571c8a85addb5bbbcf652889284d038f0eb7779b1050c71cc9f784c) (by decide+kernel)
theorem covered35:WideCovered band35 (AX band35) (tail band35):=(_Q1 band35 6553541 9364838 10642700 _DUP (_Q1 band35 9364839 10387127 10642700 _DUQ _DUR))
def band36:Band:=⟨9,51,4245,4732,8653646220513727⟩

private theorem _DUS:WideCovered band36 6684612 9530397:=PRB band36 Z1.f2197 6684612 9530397 (WB 206366726328 17 0x19dde588d471af3b0916c1dceef24563b9eaca7c837bc677792c491c59ff3a3dcb4f2bbca305ed1ec35b1cec5d95de4cb1668c14cc8d7988beef28718aedcf55c63e71df779411497532a2a2ffa46fbbc9f222b998d5317007f7dde4ee245c59ca88b01ecbaef271682df4363c541cd5d77935b2d6dd2c1a28151eebbc9a88eb5fc34b130deb75de4db5e5a83c448908a2c2df227012ed8241c445285f67910e4d685d88a1e36ac1bbc0102e01e76c30d220c0c9e00505008a8a0859461) (by decide+kernel)

private theorem _DUT:WideCovered band36 9530398 10565227:=PRB band36 Z1.f2198 9530398 10565227 (WB 206366727320 16 0xdaef3a57ba18da27d09b35eb779c9479086ebba80e71b5bbcdfae48234b5b3e7a43adde6f84b403807c9e407dd6df36c571fb869dcea1ec6b6f9aca30f9f5dea711ccf4b7cd1db07b6b1f336951da5de670353cec1189a4de9d2ef338b89e1ccf3cca8a269779950c0eebc2da6152834bbcc5f3c760020b2eaff79dde60a6a3a7a664965b56ceef2ef219cfe5d1caaf586777974908e627b0a51882f3bbcbad92725104326cacd9dde5b82038d2c009268c1) (by decide+kernel)

private theorem _DUU:WideCovered band36 10565228 10823935:=PRB band36 Z1.f2199 10565228 10823935 (WB 206366727256 4 0xdeff3ebf523e06e74a51ffb5fe7ae35469455a90b16b6bfcf0e7c8aab64d197daed779dd0e51114f0a23310) (by decide+kernel)
theorem covered36:WideCovered band36 (AX band36) (tail band36):=(_Q1 band36 6684612 9530397 10823935 _DUS (_Q1 band36 9530398 10565227 10823935 _DUT _DUU))
def band37:Band:=⟨9,52,4170,4707,12200430624772761⟩

private theorem _DUV:WideCovered band37 6815683 9695955:=PRB band37 Z1.f2200 6815683 9695955 (WB 206366726328 24 0xd2ff710bc3909f2849f969e97fb705b9ca45d3e4bcc7f4bfda1adae9042dd23e6d5a5fec353772ae1cd90f3b5caef6dbe63425a4647fa00617fb6af79781ef2e3bd12f0bfdb3e96bb132551ce8e37dfed931d5d1940a8df496beff6c2a32e4b454c6ba5e5f7fb60ad9701a72633d38afbfdb0ddcb7310d118ea0f7dded7d0a5b251a88bf52dbeef6b8d32d5d933c5baa9e16fb46a81723be1a2bd5e30b7d9e88eb904f8d13eb8985bec7c895d4774688f60fc2df65a872cee402c3fb2d616fb12e016ac76961bda9b0b7d819b8b2024890bede375bece61455a34c384f73c064f40edc01b0771423bb10317a023f403c26060fde1c13fd007b200a95c0fff168083e803d400544a077fb0e) (by decide+kernel)

private theorem _DUW:WideCovered band37 9695956 10743327:=PRB band37 Z1.f2201 9695956 10743327 (WB 206366760088 16 0xdaff613a4910eb17e8fb87f6bfd8204943222bea2ee6adaff60481108367f687badb6bbd7ecac41309bca0ef01daef5f0181009f2ae7fbd335bbd7975f3f4b14a9eef98d6ef5dc404f9b4ee677bf8f5bfd76f583da61289cf02ed6ff5d1e58f351c1e6fc1eb5bfd722803c320a69af0c5d2ff5bf040eea425667c4434bfd6d8373ad27f498f15cd2ff5b8904e8f83ce5fc69b4bfd6c03d39e006296f1f1d2ff5a64ece65348657c8f74bfd66185391ba3094f288) (by decide+kernel)

private theorem _DUX:WideCovered band37 10743328 11005170:=PRB band37 Z1.f2202 10743328 11005170 (WB 206366760024 4 0xdf0f63efa5254ff7a7ecf2df0f6303a51f24faa6ed3ddeff62a9d91a2201a5ed88deff620365160010a4edd4) (by decide+kernel)
theorem covered37:WideCovered band37 (AX band37) (tail band37):=(_Q1 band37 6815683 9695955 11005170 _DUV (_Q1 band37 9695956 10743327 11005170 _DUW _DUX))
def band38:Band:=⟨9,53,4097,4682,9076821486104566⟩

private theorem _DUY:WideCovered band38 6946754 9861514:=PRB band38 Z1.f2203 6946754 9861514 (WB 206366726296 33 0xd30fb7201b928b1996798ad30fb505d393b0b99576c6d30fb27f4392f1b9947401d70fa29e63b1337b93713dceffb3fdfb42165a926e77c30fb244faf2c859916bb3c30fb1cea2eeb53990ea51c30fb198e2eadaa49068eec30fb1cab2e5be648fe78cc2ffb16c32e273b48f662ac2ffb10a32df25448ee4c8c2ffb0a3fadbcfa48e6365c2ffb038e2d871c48de203c6efac7d0b074f988d60a1caefa878fb0e08088c5ddcc6efabde52e162b78b5b18c6efa9dcaae06f578a5853c6efa4385aec709789558fc2dfaa2582c87c568852cac2dfa81752b75515875006c2dfa25e9ac45d55864d41badfab2052a4f2a4854a7dbadfaa836aa254e484c91bb6dfa9d39a9fd1548447b8b6dfa99fca9dc68483c656b6dfa982429bc5148344f4b6dfa9632299ce2482c392b6dfa9417297e39482422f066f804e00076ed381c0cd06ef802fd8043982813f6b05df803048043791803ca6054f802168029ca07e371d041f802168029ae07a2c0a) (by decide+kernel)

private theorem _DUZ:WideCovered band38 9861515 10921427:=PRB band38 Z1.f1153 9861515 10921427 (WB 206366759960 16 0xdf0fa57fc516560e9a974f7c3e93bfe442d14a5a30edeffa457090cc67292812b7bfe8e8a1423f0ea39d85daffa2cca104742a8a6b076bfe8815f4028fea197fcdaffa1f984fd1d9e8254e36c3e850f33e61439f9273db0fa09c84f6a8fe7a3ebf5c3e7f7553ce2b69d8cead70f9f725cf025ea72289b5c3e7d5af3b6c4c9b8761d70f9ea47ceb060a6a12735c3e77e623a51cf9981d8d70f9d3230e7c94a61fc4f4c3e704ca395ae8977c4f) (by decide+kernel)

private theorem _DVA:WideCovered band38 10921428 11186405:=PRB band38 Z1.f1153 10921428 11186405 (WB 206366759960 4 0xe31fa89d992b7116aac3978c3ea04c6495fe4a9ae20e30fa72a391fef0aa2ad738c3e995d846c7d2a7a897) (by decide+kernel)
theorem covered38:WideCovered band38 (AX band38) (tail band38):=(_Q1 band38 6946754 9861514 11186405 _DUY (_Q1 band38 9861515 10921427 11186405 _DUZ _DVA))
def band39:Band:=⟨9,54,4027,4656,9304498646517170⟩

private theorem _DVB:WideCovered band39 7077825 9490846:=PRB band39 Z1.f2204 7077825 9490846 (WB 1305878354040 32 0x6187fa8a856ee3a490d19e6187fa47496cea44904eb46187fa29056ae4f48fcbc96187fa365d68d1148f48df617ffa1db967030c8ec5f5617ff9e635656b448e430b617ff9abe163cf8c8dc021617ff9736162766c8d3d37617ff9343560f2d48cba4c5f7ff8edf55f48448c37615f7ff8c7cd5d93848bb4775f7ff8d0bd5bd1a48b318d6177f751755eac9f8aaea36177f643f15fa4bf89a8cf6377f2ce9d6649e788a2fa616ff53e0d574a6e879d26616ff3b80d535b0d8697525d77f73f6d4d19ac85917e5d6ff6f5614c3ddc850e945d6ff6a1b54b6cdc848ba95d6ff641794aa9948408bf5d6ff5d06149f7d48385d55d6ff547ed495dec8302eb5d6ff4f5e548e5148280015d6ff49c6d489ce481fd175d6ff4208948a23c817a2d5d6ff365b149309480f7435d6ff227294ad41c807458db6ff133a94a3a3b7ff16e032fe04a0c06db1a7f6e840317e019dc0215797e68af02d7e011e4014a107c5d06) (by decide+kernel)

private theorem _DVC:WideCovered band39 9490847 10429243:=PRB band39 Z1.f2205 9490847 10429243 (WB 206366759000 16 0xdb1fe32f69e56a7b3e4677b63fc4e9fbbfebc678759f6c7f87170770dd6ce8bc96b8ff071b0eba9719c11bdd71fe014ddd26e0b3617d3ae3fc050939b62066818575c7f7f1c5728dd0cc80206b8fef6e20e426a197fa6cd71fddaa6dc7b2e32de931ae1faf9f93ac096657bb0f5c3f6139871bea1ca7477e787eda2becfbe1a93e31bc70fdb77b5765efb25ba8d8e1fb68342e93ed24969731c3f6c1cd5caf2248ebb96387ed6528b869e4915488) (by decide+kernel)

private theorem _DVD:WideCovered band39 10429244 11367640:=PRB band39 Z1.f1158 10429244 11367640 (WB 206366759960 14 0xe71fed6b553296d2b5d3639c7fb325c4b1118ac6f03e71febbdf526701eada4bf8c7fab35c485cb1aa635be31fe9b7cd1ba886a5761b8c3fa5297459903a857b2e30fe8673911bc629d477b7c3f9df4f434561a64c09df0fe688f10865869518d77c7f9931540fe3ea44061df1fe5a06500f4b28cea337c7f934a63f53b2a234b8db1fe3f750f9a63a84bb936c7f8dba13d7bc9a0290f) (by decide+kernel)
theorem covered39:WideCovered band39 (AX band39) (tail band39):=(_Q1 band39 7077825 9490846 11367640 _DVB (_Q1 band39 9490847 10429243 11367640 _DVC _DVD))
def band40:Band:=⟨9,55,3959,4630,9556030929267291⟩

private theorem _DVR:WideCovered band40 7208896 9344978:=PRB band40 Z1.f2206 7208896 9344978 (WB 1305879402616 37 0xc3081b56955f75568e97d261840daeb2aeb6b34709b030be06c971571241a363bb985f035c5c2b5880d1a14f8c2f81a9b55593a168c860a617c0d2b76ac0d974600cc2fbe0680cb55a221a2df4997df033993aa9d70d15f168bef819bd7953cba68a74425f7c0ce028a90c9344f7e82fbe0672a25413fba25ad797dd0331df29f136d11cdd8bee8193ff14e633688627961740b689ca5f19bc3ef03afba06077252e3e3a1b548d7dd02fb31294f78d0ca162bee81798194a28c685cc3f5d740bb50aa49a3742a3e6aeba05cd22521327a130d6d75d02d5dea9148bd087dd2bae8163e9548378683ba775d740ac9aaa41d5f419b02eeba04d04f5319cfa0ac64f75d021c56a9d121b045a42bad814cf2142357481a8af5b640b2298994ce5c0921eadb2057ebb4c721ae027f2d6d902ba18a61fc470036b2b6c8157c9130fcab7f96e759640a9bce983515bf893aacb205379f4bfecedfa38096d902803ca6254f6fc1321b2c81300f9320c537d851e034c00163e01d0c93e805601a6000b1c00e8405f1f0e80c10002600028be0f4d4e404180013180144d07646e1) (by decide+kernel)

private theorem _DVS:WideCovered band40 9344979 9989195:=PRB band40 Z1.f2207 9344979 9989195 (WB 206367774808 16 0xdb181d6bc1ccb86330d897b63031aa7baa409e5d8d9f4c607cb1767c7d94b2d41e58c0eea92bc14b995519ecb181d95817648d3299a598e303a95eae7f7825122eb1c60741f55c8ade49e224638c0e675ab7f5d8933fd6c7181cd7896d9c712576c98e103994dad7b0a248dbcb1c20722ed5a82a848d94063840e2514b41bc0912e0ec7081c0d3966c1492153398e10378962c9c4f24094ab0c206dddf58be5647d05c61840da7aab0bb488f1c45) (by decide+kernel)

private theorem _DVT:WideCovered band40 9989196 11074189:=PRB band40 Z1.f1163 9989196 11074189 (WB 206367808536 16 0xe31815caa6892e6151f51bc6302b13790cabae9fc6a78ca05479b211ba3537462f1940a57e14147b7a5dfe1df28142b42804bf349adfbbe502796b4fcd8c68f38677ca04ed601f2e5f51629a6f9409a25f3d7b92a1bc50df2812dbda799dc14166d9b65024d104f0a3ba7eaa236ca0489cf1da310cf50d26d94090fa63aaef09d98c0db2811bebe74a1f1391fb9b650227670e71bee6e1bdf6c6042c191ccc614d3f09ed8c07fb5839a2ff99752f) (by decide+kernel)

private theorem _DVU:WideCovered band40 11074190 11548875:=PRB band40 Z1.f1163 11074190 11548875 (WB 206367808536 7 0x1d650330e993abfa6c0e32faca063bdda691df5797f373940c22c64b6739ae2702e72817aaee93c5ad5a3c3dce302ebad9219bfab054eb9c605b3de237f9555862b738c0b276a45ca45aa0372) (by decide+kernel)
theorem covered40:WideCovered band40 (AX band40) (tail band40):=(_Q1 band40 7208896 9344978 11548875 _DVR (_Q1 band40 9344979 9989195 11548875 _DVS (_Q1 band40 9989196 11074189 11548875 _DVT _DVU)))
def band41:Band:=⟨9,56,3894,4604,12473176312116266⟩

private theorem _DVV:WideCovered band41 7339967 9226356:=PRB band41 Z1.f2208 7339967 9226356 (WB 1305879402616 37 0xc2f83c57215545778cc874617c1e02dca9d69fc6213d30be0eedc054a039e2ef20185f076c18aa2b0ff166d0cbef83b2d914fad3f8ab08c5f7c1d8c8ea74117c515492fbe0ec604532ea3e2692617df076106297088f123d3cbee83adcc54a10878898a45f741d4494a4a3b7c409552fba0e8b2f52285de1e32c17dd0736e7a8efcbf0e0d6cbee8393ae946ff578680bc5f741c78e4a2f7b3c2fd612fba0e2708516c87e15d3217dd07056328b751f09dd9cbee837cb6545112f8468d45f741b7a8aa2fee7c1f16d2fba0d849d519611e0d738375d0674e6295053d05adcdbae832cd0148546d8250ec5b641c0ba2979ae640e5792db20decd84bb40920513e16d906e66ca5bef79017dfcb6c836e83d2dc73c8039045b641b54a89688e63fd9852db20d8c684b520f1fcb4416d906b32a25b4258fd4e2cb6c834d1112e2a647e211c575c1b48328f8009becd912bae0d9cbd478098df454a15d706c66823b5d76f91e5caeb8360e391cae3b7c0934575c1ad3f88e5259bdc19d018e0826cd033bb09ebf5000c70405e08072d52f4ee8c06782014040141f8785f5e) (by decide+kernel)

private theorem _DVW:WideCovered band41 9226357 9775124:=PRB band41 Z1.f1161 9226357 9775124 (WB 206367774744 16 0xcb183f83bd722aaca940a658c1f9c72b8060652886b2c60fbc605b8ccf2838418e307d3b72d7d8a939626c7183e6f096a043498816638c1f3a56b3d0664a28cb1c20f987b5973552408718e107c47aac89a4917e3ec7083dda99626b9487c2263841ecb00b0739241c92b1c20f511657bd991fd8a1861079ecf2bad1c8f6656c3083cd7e55b96847702e61841e6bbcace0b639698b0c20f35bb56067d1ba8d185f07934caace738d4e6e) (by decide+kernel)

private theorem _DVX:WideCovered band41 9775125 10838362:=PRB band41 Z1.f2209 9775125 10838362 (WB 206367808600 16 0xe33835bbe0801cf1d2b0ad6f9c1a9a223f0e16e91559b7ce0d38e49f054b74692e5be70695e74f4a7f3a23d7edf38344cd679373dd098c56f9c19e8b83be64ae80965b6ca0cd16c9d996873e3345b65065f1a4ea0b9b9e0daedb2832fde873ab87ce80dd6d9419473d396cb8e6fd71b6ca0c839e1ca80b735d3a5b65062c554e55fe399dddedb28305c887332c3cc68f56d9417282f3992cda5f17db4c60c093d99ded4b2d740596305fc764ba07f095ae0e) (by decide+kernel)

private theorem _DVY:WideCovered band41 10838363 11730110:=PRB band41 Z1.f1163 10838363 11730110 (WB 206367808536 13 0x779c1e7c4e5308d5b2fcbeeb383c2810a2020963e195d67076ae353bfd52c3935baca0eb733268f93d7ec7175941d18a94b7f15aecceee7283997b09434a95b81f5ce5071d07122052eb2d41b9ca0e2526a37e1e55d489739c1c027045b30daa9d1ee3383771d088d707532255c6706db2e10c8c5aa214db8ce0dad9921086fd3bca1719c1b1dfc410e95a66d4e) (by decide+kernel)
theorem covered41:WideCovered band41 (AX band41) (tail band41):=(_Q1 band41 7339967 9226356 11730110 _DVV (_Q1 band41 9226357 9775124 11730110 _DVW (_Q1 band41 9775125 10838362 11730110 _DVX _DVY)))
def band42:Band:=⟨9,57,3830,4577,10278938603559292⟩

private theorem _DVZ:WideCovered band42 7471038 9170843:=PRB band42 Z1.f2210 7471038 9170843 (WB 206367842424 22 0xc2f84749e114cfacf8bef9bc2f847342314bf79f8b6819c2f8471c1314afd8f8ae097c2f847010914a0dbf8a5915c2f846e4ab1492b5f89d193bef846dd45147b06f894a11bef846cfb8146dfa788c28fbef846bfbe1462667883b0dbef846ac161458f1787b38bbef846927c1452caf872c09bef8466e8e14521ef86a487bef846574b143eb77861d06b6d85cc3494e0f3be859584b6d85cc7604f994c6850e02b6d85049c82c2a79e83fefebad85edc425f17c7582effab2c82461e10c0426c80d1f3b2b824166e0bb4b4c7eb3ebaeb7e28e30088b9637c95e4aea7c256870729b6a7a77dc05a8400c5e0038c717859d504884007aa00201c0763bcd) (by decide+kernel)

private theorem _DWA:WideCovered band42 9170844 9725880:=PRB band42 Z1.f1171 9170844 9725880 (WB 206367807512 16 0xcb18503e62b3bb8e519ee32c61406172cb6e893e037cb184ff064b1f9ee4d62db1c613f046ac37a192d134c7184fad7caff3ea4926cb1c613ea962bc11191c230c7184fa960ae0e7e44eabb1c213e286ab54a190b32cc7084f6540ac9e4640aeab1c213ce4b2aed0f8fa428c7084f0ed2aafcca3c729b0c213b83d2a911d8e9524c3084ecba0a98a6a38368b0c213b0ddaa33868d8620c3084ebc94a80e5233fa7f0c213aee329c0b28c771d) (by decide+kernel)

private theorem _DWB:WideCovered band42 9725881 10593128:=PRB band42 Z1.f2211 9725881 10593128 (WB 206367807576 16 0xdf38551d0cee8cf2a1a368df3854efecec1adea09465df38547a18ea6aca9f8561df3853dafce800c69e765ddf3853339ee70aa69d6759df38525570e6ec829c5855df38516552e64fda9b4951df384f0d04eb0e3a9a3a4edf384ccd1aeac621992b4acf28510506bb0cb8981c46cf2850dd0cba01089794c4cb2850b36ab8f25c970d42cb28508a60b7dfbc9685c0cb28508a36b68fc095fe3ecb285085bcb577d09576bccb185062c4b49a3094ef3a) (by decide+kernel)

private theorem _DWC:WideCovered band42 10593129 11703206:=PRB band42 Z1.f1173 10593129 11703206 (WB 206367808536 16 0xef385d93f49eff1b65274dde70b978f1363bdac6128bace16fe55a5eeb8583acf75942db9d74a2f14af669aeb485ad5da912b9d5caf2fd690b469511cfac6b5224f9d216640ba2f58ad61cc7f3a42c9095445cfcab2a8be74858ae4e868b5954370fce90b04a3108f32aa4320f8d215e09a208027d3fec071a42b877f3ff8caa6ee7ce34856e7e27e131d4bbef1c690acbb50f84d2e9341d38d215775b9ea9f751e0b86f9c2aa8a93c9b4da2b26c) (by decide+kernel)

private theorem _DWD:WideCovered band42 11703207 11911345:=PRB band42 Z1.f1173 11703207 11911345 (WB 206367841304 3 0xf3485000be55dcc0b5c0b1ef484f7d38536f47b4b1aeef384f1e2a514bd0b3a2aa) (by decide+kernel)
theorem covered42:WideCovered band42 (AX band42) (tail band42):=(_Q1 band42 7471038 9170843 11911345 _DVZ (_Q1 band42 9170844 9725880 11911345 _DWA (_Q1 band42 9725881 10593128 11911345 _DWB (_Q1 band42 10593129 11703206 11911345 _DWC _DWD))))
def band43:Band:=⟨9,58,3768,4550,24383373590804330⟩

private theorem _DWE:WideCovered band43 7602109 9110626:=PRB band43 Z1.f2212 7602109 9110626 (WB 206367909016 20 0xc30861d563428e6d988b0462c30861d24e028c10788a7b58c30861ce56c289db2889f24ec2f861c5584288cf58896944c2f861ba9b0288100888e03ac2f861af7a0287bbc8885731c2f861a5fcc28803b887ce27c2f861990e0289402887451dc2f8618c4e4288728786bc13b6d87581445b909ea6863309b6d8686989caef75a58520f6b6d8647f6085bb9bd5840ee3b6d86351bc4447988582fccfb6c862977f83658f0581eabbb2c8213643c1ac7a0480d8a8b2b82118acc17a98947eb481aeb7e0b98b012718137c9059aaa7808bce40c8d5827a6c32aa97607fb840af981178480b0658600337400705607623e4) (by decide+kernel)

private theorem _DWF:WideCovered band43 9110627 9671935:=PRB band43 Z1.f1182 9110627 9671935 (WB 206367807512 16 0xcb1870a480aeb7ae4e53ff2c61c1e642b789e930bf5cb18704f80ad310a4a0bb31c61c0819ab1ad191f9e2c718700420ab906a45c3631c61bff112aac2d90e7cec7186ff656a9ca86417b131c61bfb2caa3a098fd5bac7086fc206a8435a3d32c71c21be4f8a9e7ec8ec3a7c7086f6172a6fce638ea771c21bca662996b38db193c7086f0682a5b93234a2270c21bbd252945ee8c9f7fc3086ed78aa4cc163059d70c21bb081290cd38b8d6c) (by decide+kernel)

private theorem _DWG:WideCovered band43 9671936 10338489:=PRB band43 Z1.f2213 9671936 10338489 (WB 1305879435352 16 0x6fa439c1b173e644cee05cb7d21c71cd3a8acd672ba9bbe90dd9b99d8c19d373924cf387225d6bc44719a8a7e679c38f9235d77504d00ba33ce1c79352e6d34265e1ad9e70e3c25171012131dec2cf2871c530b799b8986657679438ce525b4ed64beea6b3ca1c5c9ead67e625d510d9e50e28ccd693d412d9672cb28711812b39a009642306594387a705948644adc93b2ca1c3bf82c6069254c0759650e1da3d60d641294e26cb1870cd1eaf8b3c941e09) (by decide+kernel)

private theorem _DWH:WideCovered band43 10338490 11461107:=PRB band43 Z1.f535 10338490 11461107 (WB 206367808536 16 0xeb587bb8708ea42d5dc3e7d6b0f6cdb517dbb2b73f83ad61eb251226523d65ee673ac3d0e00438493ababb8e7587966da847c7755334bceb0f27c1d041a4ea61e479d61e2b00a0045b543abef3a43c13103f40cca7636ae3487784207c9ec74ca2afc690ee6870f5608a94fd0f8d21dbf0a1e3f1ed21697f1a43b38313bd140a31b1ce34875d402765b5f441211c690ea7184eb885683dbd37d21d23c01d33d34ff270efa43a17a93a0d7f9ed2cd) (by decide+kernel)

private theorem _DWI:WideCovered band43 11461108 12092580:=PRB band43 Z1.f535 11461108 12092580 (WB 206367841304 9 0xf35871a2bc590972b884a4f358710c38566c80b77291f34870ab095401fdb6607df34870308051e803b54e69ef486fb6c94fd95fb43c56ef386f489e4e0e43b32a42ef486f074b4c3216b2182eef586ea3384a8f1ab1061beb586e3df148f035aff407) (by decide+kernel)
theorem covered43:WideCovered band43 (AX band43) (tail band43):=(_Q1 band43 7602109 9110626 12092580 _DWE (_Q1 band43 9110627 9671935 12092580 _DWF (_Q1 band43 9671936 10338489 12092580 _DWG (_Q1 band43 10338490 11461107 12092580 _DWH _DWI))))
def band44:Band:=⟨9,59,3709,4522,22138297435027530⟩

private theorem _DWJ:WideCovered band44 7733180 9081181:=PRB band44 Z1.f2214 7733180 9081181 (WB 206367909016 19 0xc30881de97428679888a915dc30881d994428456288a06cbc30881d3a502824e88897c39c30881c477428412a888f1a7c30881b50d82842de8886716c30881994f828815c887dc84c30881aa74827efb478751f2c2f881a3d0c27a485686c761b6d8940b3898579585863ccfb6d88878f5ca7013848527acb6d884aaa005a2f824841288b6d8837a99c440785482fd65b6d882bd9cc3680fc481e841b2c88237b702d45db480d31eb2c881cba3026658c47fbdfab2b8211e8ec16f7c537ea8d7b2b7e0c2c3412c25227c7e90aea7c0a546c0e66ce17a5449aa9760820180aac710782a02) (by decide+kernel)

private theorem _DWK:WideCovered band44 9081182 9648760:=PRB band44 Z1.f1182 9081182 9648760 (WB 206367807512 16 0xcb189134f6abdde24ce9e32c62441742ac2b592afe6cb1890d6e6aa59524895531c62429062a5dda919ac3c7189097cea8a9e64440c71c62422e129f9a490859fc718908446a6f3523fec371c6241c7f298e118f707cc708904374a5a3e23b97af1c2240397293eb98e5b59c7088fd8f8a487f237431f1c223e62d28fbbc8d4635c7088f7e9ea34a9e32ee930c223d77ba8bea28c3112c3088f43eaa25d9e2e9a030c223ca06a870338b1bee) (by decide+kernel)

private theorem _DWL:WideCovered band44 9648761 10287287:=PRB band44 Z1.f2215 9648761 10287287 (WB 206367807576 16 0xe34891ae28eb53529cf8b7e3488efba6ebd6659be393d33892f4ecba11689ace70cf3892c752b90b849a43decf38929800b7cd3099b94ccf3892914cb687fc992ebacf38928ac0b5759098a429cf289262f4b46bc4981998cf2892362ab36648978f06cf28920c98b2906c970474cf2891dbacb185a09679e2cb2891a806b0761095ef51cb289195a6af9a4c9564bfcb28918f6cae7f8894da2dcb28918866ad61f4944f9bcb1891624cacb88893c50a) (by decide+kernel)

private theorem _DWM:WideCovered band44 10287288 11422446:=PRB band44 Z1.f535 10287288 11422446 (WB 206367808536 16 0xeb689cbc908be6a95c95ddd6d1386c6d11ee46b4d72fada26e3a9a1aad9d61053f3ac4d70be423482ab0b84e7589a4dc681adb753ecc1ceb1340e2cff544ea384f79d6265d9d1f7ee8d3e60d71ac4c628f3df28ba6b6f6e358981c967a4a634b43a7c6b12fdd18f179a69232bf8d625e8b29dbc30d1bbc671a44b8a3a3afe0da26268e3489671d475386b429a8bc6912b1694e81a2e80e0878d2252d061cf88ccf917f71a449ca2f3a47a09e0dda) (by decide+kernel)

private theorem _DWN:WideCovered band44 11422447 12273815:=PRB band44 Z1.f535 11422447 12273815 (WB 206367841304 12 0xf76893deff5f0388bb4897f758935b525c157eba3374f75892c1265986b1b91e50f358921f5856d97eb8092df34891843d54535ab6f409f358912e86523157b5dee6f36890b155502fcbb4c9c2ef68902e264e19f6b3b49fef688fcaa74c3829b29f7bef688f7e654a9c5eb18a59ef688f0f1d48e4d9b07535eb688eaa27476ae1af6012) (by decide+kernel)
theorem covered44:WideCovered band44 (AX band44) (tail band44):=(_Q1 band44 7733180 9081181 12273815 _DWJ (_Q1 band44 9081182 9648760 12273815 _DWK (_Q1 band44 9648761 10287287 12273815 _DWL (_Q1 band44 10287288 11422446 12273815 _DWM _DWN))))
def band45:Band:=⟨9,60,3605,4495,24443499782550246⟩

private theorem _DWO:WideCovered band45 7864251 9011950:=PRB band45 Z1.f2216 7864251 9011950 (WB 1305879536760 17 0x638450e9ecc13e059e8982eee18450e646a13aecd588f6d55f7c50fc882126fe2c886abb5f7c50fa05412656f487dea15f7c50f7a221250e048752885f7c50f3090124d34c86c66e5b6c5bfee4acf5d3eb863a545b6c550212a57e178a8522215b6c52aa7fe2dd6bc28409ee5b6c520087422da31282f1ba5b6c51989201c48d1281d9875964515075617f4e7280c154596450f9c3212b68327fa921596450ee33610b11427e90ee596450df15410370427d78ba5753e0659b4071c3317c60875753c050c5e064f0f07a3021) (by decide+kernel)

private theorem _DWP:WideCovered band45 9011951 9585800:=PRB band45 Z1.f1188 9011951 9585800 (WB 206367807512 16 0xcb18b2622ca593864912232c62c8b5d29418f91b86fcb18b1f402a47dee44b1572c62c6c9aa8ee1290a03bcb18b1962ca3371640508b1c62c5fb8289ba18f8808c718b15eb8a1f5923befbb1c62c4fcb2858448e6fd5c718b11ff2a0b8e2378eef1c62c3c9ba816718d57a1c718b0c58e9f9f2a332e231c22c1c88a7e0d58c3f6ec708b01de49f2aa62ecd531c22bf46927d1fe8b273bc708af6d3c9fa0aa2a6c871c62bbbfba7f8198a0f07) (by decide+kernel)

private theorem _DWQ:WideCovered band45 9585801 10159650:=PRB band45 Z1.f1188 9585801 10159650 (WB 206367807512 16 0xd338b4ada2b482da6c188b4ce2d1e9aacdeaa9a7a09d338b444beb26da267b7bf3ce2d03f02c5e669961d5cf38b3e830b04b266356f33ce2cf690abd3f69849a2cf38b3d02eae124e5ef6233ca2ceb912b4e7097316fcf28b37fdeac777e5a95573ca2cd23f2ae04b96193bcf28b314faaabe5e56348b2ca2cb635aa7054950108cb28b2c718a8fb3251d3bb2ca2cad722a0d2493e8d5cb28b2a9cea725a64d72ef2ca2ca64029964e92d0a1) (by decide+kernel)

private theorem _DWR:WideCovered band45 10159651 11235619:=PRB band45 Z1.f2217 10159651 11235619 (WB 1305879436376 16 0x75b45eb8df406901eadc48dd6d17960c0fd72b7aa58f073b45df0ae3e5264ea502f1ced1773320f51d33a8288973ac5d98943c65ede9c4159ceb1750494eebd5fa5f82273ac5cecd53b4035e937fbdc6b171ec5cea9757a3c7bc71ac5c3d6e3a2030e8abe25c6b17004ece6f03fa1975671ac5b9c0d399a78e81fc89ceb1682aa8ed30db9f66eff1ac5821613bd096a793af1be916a9320cdb5c59d368869a45a7cbf2daf172707955a67169b8e4b573249b923b) (by decide+kernel)

private theorem _DWS:WideCovered band45 11235620 12383319:=PRB band45 Z1.f539 11235620 12383319 (WB 206367841304 16 0xfb68b67f655f2f0abcf457fb68b5b1fb5c1fd8bbdc24f768b4e8c059282ebac3f0f758b45c0b565294b9abbdf768b3b99453f4f0b8938af378b3291a51ea88b77b56f378b288e74fa672b66323f378b22b9a4d8791b54af0f378b1a9424bb773b432bdef78b1262f49ee47b31a8aef78b0a54c482870b20256ef78b074e846c214b0ea23ef78b008ce455b71afd1f0eb68af9a0f43f854aeb9bceb68af2b814295b1ada189eb68af0919414570ac8956) (by decide+kernel)

private theorem _DWT:WideCovered band45 12383320 12455050:=PRB band45 Z1.f539 12383320 12455050 (WB 206367841304 1 0xfb68b72b0b621ef9be0c8a) (by decide+kernel)
theorem covered45:WideCovered band45 (AX band45) (tail band45):=(_Q1 band45 7864251 9011950 12455050 _DWO (_Q1 band45 9011951 9585800 12455050 _DWP (_Q1 band45 9585801 10159650 12455050 _DWQ (_Q1 band45 10159651 11235619 12455050 _DWR (_Q1 band45 11235620 12383319 12455050 _DWS _DWT)))))
def band46:Band:=⟨9,61,3549,4466,25443885488722536⟩

private theorem _DWU:WideCovered band46 7995322 8883631:=PRB band46 Z1.f2218 7995322 8883631 (WB 206367908952 16 0xbef8c1f742824ab7ee1e36befbe307c9c7092b0cf8746debef8c1ee57424a0a0e1c003adb63671bdb6904ae586b93db6d8b364bf540d752a18ae6edb632663872854eac851058b6d8c568ca059074120fd452db6310877c113a17882d9d1b6c8c309e0833a690206fa3ecb230a1a110b10b7880a34cb2c8c21e08427479e1fe2026cb2306d6280926d047e6cc5b2c8c1c6f5c1fe9561f5460acb23067a7907ebebd7c363faeb8c12fdd81479a21ec6bf2bae3048ea104fff9c7a8d5a) (by decide+kernel)

private theorem _DWV:WideCovered band46 8883632 9409365:=PRB band46 Z1.f1193 8883632 9409365 (WB 1305879435352 16 0x658c68cb3f50576047c9aab2c63456a9281a3e23c16d19631a241294071291cf024cb18d0d9b2a026388dea70658c683fce501f0e46ae67b2c63408a1a802802333cb78e319efc01417921188319c718ce9f32a194538bb3eae38c6760514f285f459324b0be341caea4dcae62a62a185f1a06f9d2650bb14160cc2f8d014e892a3ad897d65617c67f2aa4936a8c477e1b0be34025b24cb34221888585f19fd9b1263b791036a2bef8cfd46292e52087d480) (by decide+kernel)

private theorem _DWW:WideCovered band46 9409366 9989486:=PRB band46 Z1.f541 9409366 9989486 (WB 206367807512 16 0xd338d424a4ac811261b5bb3ce3501132ae04b97dfcccf38d3f3f2aa70ae5d48af3ce34f8e02a5fc696c489cf38d3ceaea8937658dba33ca34e6a0a9f8ae95a946cf28d362caa733f2546e933ca34c9ad29a1c8948e03cf28d2e504a59c1e50018b2ca34b2ec293bb59372c1cb28d2b192a4431e4b947f2ca34a5a2a8e61592577dcb28d27a52a2eed64727732ca34972b28918b913c3acb18d23160a172f642ba632c6347a152841459020f7) (by decide+kernel)

private theorem _DWX:WideCovered band46 9989487 10750894:=PRB band46 Z1.f2219 9989487 10750894 (WB 1305879435352 16 0x73b46cfc0f745cd7d205d739da3644d23a28f5e8bc1adced1af0581d5a83743aa4fe768cf46e4f7e00aa0b9e46fa46b79e2674968cfcf50b5d2358700adfac427a0d79ae91abccad6db0793beb78d748d5aec6b5c40c9d681b6ba46aba7f5a57064e6d3d34d2354ec2ace5432713361a691aa54c964f139377e6ed348d51cd8b119f09b3195699c6a7fe95807ac4d51f9b4ce3533402bcb292685949a671a92fb15c9339331160d338d45fe8ad65f898fb0f) (by decide+kernel)

private theorem _DWY:WideCovered band46 10750895 11911135:=PRB band46 Z1.f543 10750895 11911135 (WB 206367841304 16 0xf388d268394c018db5bfdff388d21a0f4a24d6b4a49cf388d1a43e48a6e3b38959f378d11e5946f3b8b26e16ef78d0a436458133b152d2ef78d06fd0441130b0378fef78d0073642b3baaf1c4cef78cfa1b9419a7aae010aeb78cf376c408785ace5c7eb78cefa9d3f63a8abca83eb68cec4003e4bf6aaaf40eb68ce6afa3d8b72a993fdeb68ce0aa03cd8d2a878bae768cd961a3be9e9a75d76e768cd70803b518fa64233e768cd43a13ad4e3a526f1) (by decide+kernel)

private theorem _DWZ:WideCovered band46 11911136 12636285:=PRB band46 Z1.f543 11911136 12636285 (WB 206367841304 10 0xff78d991fc672495c0d07dff78d89e4763a310bfb53afb78d7b287604685be99f7fb68d6c65b5cee5ebd7eb4fb68d626c759dcb9bc6371fb78d56f17574e26bb482ef788d4ba3754d281ba2cebf788d42352521796b911a8f788d39b5150144ab7f665f788d30a524e285cb6db23) (by decide+kernel)
theorem covered46:WideCovered band46 (AX band46) (tail band46):=(_Q1 band46 7995322 8883631 12636285 _DWU (_Q1 band46 8883632 9409365 12636285 _DWV (_Q1 band46 9409366 9989486 12636285 _DWW (_Q1 band46 9989487 10750894 12636285 _DWX (_Q1 band46 10750895 11911135 12636285 _DWY _DWZ)))))
def band47:Band:=⟨9,62,3495,4437,21355490135861018⟩

private theorem _DXA:WideCovered band47 8126393 8932680:=PRB band47 Z1.f2220 8126393 8932680 (WB 1306953278584 16 0x60c2387dc2e092700a4426a430611c3df928494c4b22016d18308e1e459424c10690f7c3ec18470e75fa12824a487768ae1c238661680972621c3977aef611c3c27c048bba0a1b9d856ad8d5ed0e557108130d3f98b56c6a6d40ea5caa198610a25ab6329338229a4150427927ad5b18a4f870a3119420f4ff56ad8c407514409dea1056b54b56c61a93dc1b342e081975758b230a2c220ac615c403c822c5918456fd04e90021fd6ac562c8c1f2d90206fbb0fc78bcb16460a9be611b61b87d1e0b) (by decide+kernel)

private theorem _DXB:WideCovered band47 8932681 9372473:=PRB band47 Z1.f2221 8932681 9372473 (WB 1305879435352 16 0xe594785b2f5074ca47819cf2ca3bf9b2286d0f239d03f9651dcd9b5479aa11bc9cdcb28edcfb8a339368d55bd6384788ff349cf22c66349b1c23c3d5024d6b6630dda98e11e1912525f9db175080c308f094c692aa7d8b19176184785c8d49b6be4544f6b0c23c275324ce9022909658611e0fdf926134113f588c308f05d8492dcac89b3306184781c1c4959fc44b5cd30c23c066924a45122490198611e0014124ee5911b8e4c308efe15e9269cc8894dd) (by decide+kernel)

private theorem _DXC:WideCovered band47 9372474 9958864:=PRB band47 Z1.f545 9372474 9958864 (WB 1305879435288 16 0x699c7a317454743d2feba0d338f41ebea8181e5d9a9d9e71e7fdf14e8cf4b6bbeb3ce3cf97ea99cb7964854679c79e69852ce2f2b7256cf38f3b4d4a4c15654a8059e71e7377d47c65ca4d6c33ca3cd67928d3fd940bae67947988975160f926f90acf28f2c058a239c24bb56d9e51e521ad4410a492f1933ca3c987f28663a91cf08679479163e509b85227fbecf28f1ed98a0e7da42c2d59e51e34189416864810c672ca3c4f8c282aa98f9262) (by decide+kernel)

private theorem _DXD:WideCovered band47 9958865 10545255:=PRB band47 Z1.f545 9958865 10545255 (WB 206367807512 16 0xdb58f729bab98efe83a19f6d63dba9f2e1545a0593dd758f6a8bcb717ce7f28535d63da1c22d758b9f3aebd758f674d8b48eba7aaf075d63d98ec2cdb819e1c98d748f62ddcb278ce7635bb5d23d7d062c5d5b9cfe45d748f5b7b0b0704a71bc6f5d23d5e0aabda339bdff2d348f5499eae5dca6d43234d23d4d7cab53a99ac1a0d348f523b6ac397e68c9db4d23d43bcaac95e99a34dd338f4d6c6aa52f264508f4ce3d273e2a63909884fa) (by decide+kernel)

private theorem _DXE:WideCovered band47 10545256 11718037:=PRB band47 Z1.f2222 10545256 11718037 (WB 206367841336 16 0xf388f1876945a584d966caf9c4788d94223d286c6bd0bbe23c279290c8b376121dfdf11e07ec0838e0faf729cef78f00aaa408966d72a24f7bc77d0439fc1e26b4d7dbbde3bcd9d0fa86bb582f49d6f1dd894a7ba7cfaaf951eb78eea0e03ce519d4ed7f75bc773afb1e0653ea2f2afade3b82fccedf0674f3cb3d6d1db1f9e760cdfa68006eb68ed0af53b22ccd2b0d9f5b4761a449d9ee3e910d83ada3ac3e00f0623b464a1bd6d1d43f5a76aca2a206ba) (by decide+kernel)

private theorem _DXF:WideCovered band47 11718038 12817520:=PRB band47 Z1.f547 11718038 12817520 (WB 240727579672 15 0x40e23f0aee5b431030e51c20711f621acd2462984ec3aff78f9e6a365038bc157ca7fbc7c834db08c3ee01cbbbfe23e06a8d777baafc6c91f731ee69a8b586217bf9a4fb98f668ce581346bcde7f7dcc7aec8caaa7b4dde0163ee63d48dfd4baea2ea8765ef31e8de8ea12c9773070ef798f3d44f4e4ab2b865347bcc79b9ff26462fdba370bde23cb87c52aefeed8a239e711e49c5491e4e56a1476f388f1e349472b98b3ebe8) (by decide+kernel)
theorem covered47:WideCovered band47 (AX band47) (tail band47):=(_Q1 band47 8126393 8932680 12817520 _DXA (_Q1 band47 8932681 9372473 12817520 _DXB (_Q1 band47 9372474 9958864 12817520 _DXC (_Q1 band47 9958865 10545255 12817520 _DXD (_Q1 band47 10545256 11718037 12817520 _DXE _DXF)))))
def band48:Band:=⟨9,63,3443,4408,21017180655268888⟩

private theorem _DXG:WideCovered band48 8257464 8961249:=PRB band48 Z1.f2223 8257464 8961249 (WB 1306953278584 16 0x60c2407f1f70919896445e70b061203ef62048c40b221d225830901eaca42485f09105861c38480eb52e126393c87e3d7e1c24070186094223a43cdbf70e120367d204a1c68e1d4c9b7ef901f376023a7e050e159bbf7c80f5e4211d67f286c2755ab635773b75267b30c33d0e2d5b1aa70cfa8b060e617a5ad6ad8c985f2494c62f1099010b56c6292b8a274082083a6a55ab631074450fee1dc4142a12d591863f750630e822058f7d62c8c2b4a3c2c9acf10084f8b164610926a1280f287f2119) (by decide+kernel)

private theorem _DXH:WideCovered band48 8961250 9405746:=PRB band48 Z1.f2224 8961250 9405746 (WB 1305879435352 16 0xe59488a9584fe1a847c29972ca442a7ca80e2223bd20396521f437d42cdf11cc79ecb29100cde9d8a3a8dd31d638488cfd84922f4c6a13631c2445e3ca474b4632c6e98e12228cd9235ea3184212c7091113f89150a98b90576184889c074901d6457fd3b0c24446462479de22add3d861221edb123a1f114ddeac30910d9b4918a408a269d61848857e248bfb444ef2230c2441fd3a4602622657b1861220ace5228b31129b26c309101f8891613c89053a) (by decide+kernel)

private theorem _DXI:WideCovered band48 9405747 9998407:=PRB band48 Z1.f545 9405747 9998407 (WB 206367807512 16 0xd339152900a78b6a62411f4ce45397ea9ac8c97ff95d33914a58aa6158e5dbb934ce451d60a94f0796de32cf391459d0a45fde5936073ce450e4ea8f2e695bcd0cf39141cd4a2eb4654b07b3ce45003e2880ef949b6dcf3913db1ea176a6502af33ca44e387a838f7937a0bcf29133a5ca06c524ba5673ca44bdc12807e89258a8cf2912c45c9fa8c6471fdb3ca44a00a27e5cd913745cf291237ca9f55b2429a4f3ca44783527c9b49015e2) (by decide+kernel)

private theorem _DXJ:WideCovered band48 9998408 10628109:=PRB band48 Z1.f1199 9998408 10628109 (WB 206367807544 16 0xe3591913aace9d0744581bb6b22f9f796ef2b2842aaf6d645e34d2d8df8503cfcebac8ba42e5a7a849fe948d7591713c2b3e2413eb12daeb22dfce56528e27b1f975d645ba992c594c4f1b99eba48b62965823d69da682d749168826af3bf53a2ba3ae922c9eb15cc7ca7214835d245831eab55474dfa37e9a48ae6675621389b63bdd34915b4e8ab68b535a619a6922b3f01549aca69096b4d24562f42a4a814cd8d4e9a48ab3db5431d69920f7) (by decide+kernel)

private theorem _DXK:WideCovered band48 10628110 11813432:=PRB band48 Z1.f2225 10628110 11813432 (WB 1305879469112 16 0x79cc89352ea3863f6d108e1e7322465c88aefc1b320d679c488df01221c7d6c7fdcde712226a848584f7b0de1077c4885b8820c7ff6bef2b5df1221108080c4abae9b4b77c48819741f9da66b5e7a5def21f8b507cae1dac588677bc87a9a31ec7e16acdc8dd6f21dd5a679b45faa15c175bc8764ca9ded736a3d179d6f21d2eaa7696f1a7d2fb75bc8714891d8a64e9ac661d6f21b126c7575e9a5903575bc8664e61d9452e91bb4bd6f20f707e7e4394a34d6f) (by decide+kernel)

private theorem _DXL:WideCovered band48 11813433 12998755:=PRB band48 Z1.f547 11813433 12998755 (WB 240727612440 16 0x83cc8822205e476d319618e07321ef07b7398f3c5370181c4876aea9b969d710567a07321c583369c87dc2f43b7fcc86cae71972bf7074b61ff521a099f61fabcc0b1767fd4864b9f178e366fe404dff5218494e5b3ff6be6eb07dd485da541618752f53535f75216a74455431fbc2beb7dd485809ed4bc9f2ec2a21f73215518950c223b9e9267bcc85260f139f5e6e31f0def32142b274c40f1b7a6617bcc84e73e12a499ada13f9ef32130e1e48eeafb5639b) (by decide+kernel)
theorem covered48:WideCovered band48 (AX band48) (tail band48):=(_Q1 band48 8257464 8961249 12998755 _DXG (_Q1 band48 8961250 9405746 12998755 _DXH (_Q1 band48 9405747 9998407 12998755 _DXI (_Q1 band48 9998408 10628109 12998755 _DXJ (_Q1 band48 10628110 11813432 12998755 _DXK _DXL)))))
def band49:Band:=⟨9,64,3393,4378,19799739627461740⟩

private theorem _DXM:WideCovered band49 8388535 8987466:=PRB band49 Z1.f2226 8388535 8987466 (WB 1306953278584 16 0xe1c2487bc92091222a4491a570e1243deb9847c950e2368b7870921df4042417c27112222bd7c910dbb610ce9128847f55ebe48864c308625c943ff6c2f5f2442c658430292a1ed6f17af92213d8821761150ed93cbd7c9108b0010b59428723825ebe4883a9f0858cad436d32af5f244174f842bb8ea1a45256ad8d4399c527222e10c9058b56c6a3c9689833db185b5f25ab631ef6c01d5d4204248c02d5b18acd4489fae1220db4396ad8c3f85e83bb3d41049136b564618989e17bc788812428) (by decide+kernel)

private theorem _DXN:WideCovered band49 8987467 9324365:=PRB band49 Z1.f2227 8987467 9324365 (WB 1306953177176 16 0x62c64c7b23a479b8e391d358b1931b90a91599b8db51462c64c746b249849a348b6d8b1931b3d4921b3a8cd9bf62c64c644ca4791aa3242898b1931712e91d5ce8c478662c64c58d1a465d1a2ff9a18b19315438915ab68bb54c62c64c48022461c0a2db0bd8b193104d29162ca8b231362c64c3826a453ffa2b67d98b1930627e92133e8a90d962c64bfb3ea4a8a6a291ef38b192eddfa94640e89fea0e1c24c0247244e23626d60f87092fd40290d608896c67) (by decide+kernel)

private theorem _DXO:WideCovered band49 9324366 9923297:=PRB band49 Z1.f2228 9324366 9923297 (WB 1305879435352 16 0x699c9a7dcd51c8c94bb570b4ce4d2d45a8c541a5b62a1a67268bc8144b8452c8cded339342366a1f05295b436699c99fc48509fcb4a90fe34ce4cf079a83ae7a523f0da6726703d5415d7527fb14cf39334406a01cc2936b50679c9973c4500d83496c8bb3ce4ca20627f18ea491b799e7263ccd1408e7523694bcf3930de3aa1a0b291226ce79c97beef51b28f48481933ca4c6339a722fe63ff7e5963264a1b92501991ed780c7193222f09226e08ed986) (by decide+kernel)

private theorem _DXP:WideCovered band49 9923298 10522229:=PRB band49 Z1.f551 9923298 10522229 (WB 206367807512 16 0xdb5937e1f4b2b8d28239d76d64de9052c6f199ffc3cdb5937639cb0c07a7da80f5d64dc60cabe2849ed7cad75936f566ae8a827916435d64db7692b524a9db357d75936c604ac41e674847b5d64da948aad2cc9c8ee4d749366226aa50066ff2af5d24d88b42a63099b6a72d74935d74ea88e026b60e75d24d68f7a9f2ea9a4600d34935856aa70bae66cf1b4d24d5a79a9811999218dd349354adea542d2623d534d24d4c49290b3e97fd1a) (by decide+kernel)

private theorem _DXQ:WideCovered band49 10522230 11532927:=PRB band49 Z1.f2229 10522230 11532927 (WB 206367841368 16 0xf3893119b040c8bfebfe9ffbe24c25544fecc73aed60cef893026383ea3e7eb6c66bbe24c00c0cf665afac8d28ef892faad43ccce8eada2d7be24bd06acf1fd37aa4442ef892eafb83c0bd5ea47f43be24b7d650ef379ba7fb5eef892d3cb63bf38ae9b5bafbe24af32b8f4ad2ea5b278ef792aa8623c4b90692381b7da4b17f40b90aa8a36994db692c3ca22df4e828b5d6b6da4b0aff4b69a74a24521db692c20242d47f3286cba36da4b048d8b3e7dca120ae) (by decide+kernel)

private theorem _DXR:WideCovered band49 11532928 12730791:=PRB band49 Z1.f554 11532928 12730791 (WB 240727579672 16 0x81dc9dac00b17612e120d3bfee4e94eb97ea2330474d1ff72727842b84e357ff184ffb93883da58f349bed4507fd49bd2a52b19f65ed7eebeea4db27854e23faf22da9f7526c316ea2803176cdf0fba93595cf4ef820ba42867dd49a7313a675b5dc8f09bdea4d0d4f92ba0d6dfe681ef52678b8891d3e96daa5cf7993358ad478498b5b0bc7bcc9963eca2fd1c5a4624bce64c8c97d11d4cacd9f59e73263ba9c85e3816486c8f39931850d41a7b7b11ef2) (by decide+kernel)

private theorem _DXS:WideCovered band49 12730792 13179990:=PRB band49 Z1.f554 12730792 13179990 (WB 240727613464 6 0x20f52642aba41107f648e2b41e64c4358e7b2bbcc7f7e483cc982e43ceb425f8da6e307a92f93a11c18d6316bbfa07525da98835b8a5e2454640ee4b8f94a66be46c3661a) (by decide+kernel)
theorem covered49:WideCovered band49 (AX band49) (tail band49):=(_Q1 band49 8388535 8987466 13179990 _DXM (_Q1 band49 8987467 9324365 13179990 _DXN (_Q1 band49 9324366 9923297 13179990 _DXO (_Q1 band49 9923298 10522229 13179990 _DXP (_Q1 band49 10522230 11532927 13179990 _DXQ (_Q1 band49 11532928 12730791 13179990 _DXR _DXS))))))
def band50:Band:=⟨9,65,3343,4347,25044443039245876⟩

private theorem _DYG:WideCovered band50 8519606 9011332:=PRB band50 Z1.f2230 8519606 9011332 (WB 1306953278552 16 0x60c2508907708612a689808460c2508846a085ef528936a460c25087782085ce8a88ecc3dec25086997085b0da88a2e3dfbe5085a7d08596b688590260c255692815492b53880f2260c25553d675481f2787c54060c255444795506047877b6060c2553ba2f564bb4f87317f5ebe5085325082aad286e79f5ebe5084d600829bea86c2ae5ab635c41185128889869dbe5ab633b7e85349c1bc8609fe5ab634ef951474d96c85763c5ab631c66581a3c7a4844eba5ab631324c9112db40832737) (by decide+kernel)

private theorem _DYH:WideCovered band50 9011333 9313934:=PRB band50 Z1.f2231 9011333 9313934 (WB 1306953177208 16 0x64ca547dae248f73b1c3d1cc994a8e722491b4563752b9932951a142923822c6c56632652a2dcf9248a858d40ece2ca544d24249814b19ee17c78ca878b24946c3632b4af8f1950a22092d24ac631a571e32a0b0912582a48c196ae3c654025124a8f17179f13c78ca7ece448f302a2e16a38f194f576692a725459de3f1e329f78c52171818af1e7e3c653c09e247926315500ec184a8b08a4344b2229789d8309514ce0865ffc450a2330612a26f110c70c889ca66) (by decide+kernel)

private theorem _DYI:WideCovered band50 9313935 9843486:=PRB band50 Z1.f2232 9313935 9843486 (WB 1305879435352 16 0x69a4aa285d5093484b198f34d2550074a8349b2567d75a692a73d0d4147292a1736d3495318b8a0b3bc9477da69a4a93db050a1b049f20d34d2547b8c285c7224d4163a6929e4f494cd93125792fcf3951f42c9d94ca9228d6e79ca884b54f5be948ca8ab2ca54b3fd249479644054d9652a5305923ca4b20db24cb295257ba917d358fd9d16594a93c44494d7447a30832ca5496f5249f0123bf0c19652a479d924c3411d649ecb29521b60924ca88e686f) (by decide+kernel)

private theorem _DYJ:WideCovered band50 9843487 10448689:=PRB band50 Z1.f557 9843487 10448689 (WB 206367807512 16 0xdb5957af7cad757e7dbcc76d655da462b1e689edb6fdb59572172ab911a791ebb6d655b75baaaa269db3edd75956be9aa9bfee7480b35d655a7f4aa35839c8c6bd759568124a7ea666fe2ab5d65599bd29ab449b64e9d7495629c2a5f19a6b449f5d2557824a952ad9a3d66d7495590d0a4a93666a6975d25554caa903739915e3d749552764a3799662088f5d2553def28bba497ee62d34954cb94a20faa5d6a834d25524a5a864b396c6df) (by decide+kernel)

private theorem _DYK:WideCovered band50 10448690 11243016:=PRB band50 Z1.f2233 10448690 11243016 (WB 206367807576 16 0xef895e9318f3fa62ab8e08ef895da682f3826aaa6686ef895c7fdcf2797aa93f04f389593390f88c22a81781ef8958b3b4eea5ada6efffdf7959c62abad0a4a5c87ddf7959aa38b96a68a534bcdf79598fd6b7fed4a4a0fadf69595954b6c8d8a40d3adf6959134cb595e4a37979df6958c842b45000a2e5b7df69587f36b32c18a251f6db69584560b20628a1be36db695829cab0dd90a12a75db69580f5aafb094a096b3db6957f4c6ae8138a002f2) (by decide+kernel)

private theorem _DYL:WideCovered band50 11243017 12453421:=PRB band50 Z1.f559 11243017 12453421 (WB 206367841304 16 0xffb957e2545433c5be062dffb95708ae51a6a1bcdeacfbb95646434f7706bbb729fbb95588f64d54caba8fa7fba95519d44b1d01b96824fba9547d6f4974f6b840a2f7a953dee047d86ab71920f7a9535507464427b5f19df7a953042d448a7cb4ca1bf799528232435ac8b3a299f79951facb42374ab27b16f3995172f740cf6eb15394f399514af43fba00b02c11f39950ed443ee944af0490f39950709f3e372daddd0df3894fd3953d6419acb58a) (by decide+kernel)

private theorem _DYM:WideCovered band50 12453422 13361225:=PRB band50 Z1.f559 12453422 13361225 (WB 240727613464 12 0x85d4aa1e50d19d3e797c0930ba9530b1ca1304532ae31e1752a441313f0ebd64c8a241ee5447980778b34c869c383dca81f840e3dccf8e848107c94f9dd01b3c723186afe0f929dc4c03420c762799e40f2538f86c64382ac3cbb981e4a6db428c0b74d85486f03b94d3b7c173ee0305f2d5ff72996ede2ce721602a99bfee530f25e56eb5abf2db0) (by decide+kernel)
theorem covered50:WideCovered band50 (AX band50) (tail band50):=(_Q1 band50 8519606 9011332 13361225 _DYG (_Q1 band50 9011333 9313934 13361225 _DYH (_Q1 band50 9313935 9843486 13361225 _DYI (_Q1 band50 9843487 10448689 13361225 _DYJ (_Q1 band50 10448690 11243016 13361225 _DYK (_Q1 band50 11243017 12453421 13361225 _DYL _DYM))))))
def band51:Band:=⟨9,66,3295,4316,27465026451843380⟩

private theorem _DYN:WideCovered band51 8650677 8975521:=PRB band51 Z1.f2234 8650677 8975521 (WB 206367908984 16 0xc719732d77d625356711e9438e32e697df3011ce2e22a7f31c65bd6344509d5b3c42fac638cb77543ea73ca77883a07c30975509d942dd3191029698e32d9206c33506b1a1f28431c65a3980f60fd44ec3d25ee184ba121c09d9376c877f6bc71962ed2ab18b2b670e698f8e32ef3d5aed98b90e1c3dd30c25dc2c545d62d594375116184bb79e78bcad2f286c4d0b6d8d7b7b8543cd9b30d3efb6db1ad764726e484e2195362db632d1ade26cdb8042dfc7db6c665d87e59b2508852a46) (by decide+kernel)

private theorem _DYO:WideCovered band51 8975522 9281258:=PRB band51 Z1.f2235 8975522 9281258 (WB 1306953278584 16 0xe5ca587e6ed093d7eac6cf7532652c41960848b87d2355117972961f493824a2e691a1342c58cb11f8a810e11fb8cbefd62c6588f1ff086c875c63a2cb1612c472f88435354e30a6d383096236a3c2199c9717be1fc184b1199c610c93cb8b946a60c2588beaf086258dc5a4e330612c45823842fa4ee2bfc85932969e8f654b750951568fac58cbbc0126b773bd18a69d862c65dca8c45c3fba8c50f9a31632ede9d7aed9146627523d8b197387bd148ba2b11313d6c58cb9a4a12a8e5810893f45) (by decide+kernel)

private theorem _DYP:WideCovered band51 9281259 9606103:=PRB band51 Z1.f2236 9281259 9606103 (WB 1306953177176 16 0x66ca5ccb21a490bce4a4f5d9b39733f9c93cdca91fe8e66ce5cc8fe24e43aa46cfa99b397302ec937dc291694666ce5cb8d424d1b9a447a859b3972bc60933f5e90d3fc66ce5ca44a24d045a42256397297267c29319fe903eb3e5ca5c8c7e24cc16a3fd03f972971fe02931a5e8fa96ae5ca5c6de8a4d42fa3d7b1b97297172329358728f1421e5ca5c43db24f15aa3b25f7972970a9b89406568e7ed7e5ca5c057e253265638d0cf97296fd6a0949db48de98e) (by decide+kernel)

private theorem _DYQ:WideCovered band51 9606104 10217575:=PRB band51 Z1.f2237 9606104 10217575 (WB 1305879435384 16 0x6dacbb2dc852e51526fa19daeb2ec61f14a0e4c9b531e6bacbb020952236326af759aeb2eba8a94711bc9a288d6bacbad07b5166cf2664d11aeb2eabb8144e30498fdfa6bacba8b4950f5e3261a2c5ae92e965f54310fc97d3686ba4ba33d650a79925cf87dae92e81c09426c7496a8d66ba4b9cf9f50a5bb2584e35ae92e61f51434d94957e44e9a4b93dbe50a89ee53a3efa692e36f7d42842a9453b2e9a4b8878f50182064ef9a59e52e6bc69253d28932920) (by decide+kernel)

private theorem _DYR:WideCovered band51 10217576 10829049:=PRB band51 Z1.f562 10217576 10829049 (WB 206367807512 16 0xdf7979a4d8b5feaa94f3e77de5e60922d2b29a4a7b0df79796480b37bce9049a37de5e51fb2c8f45a37d1edf69790d0eb11a928b9f577da5e311c2c0362a2528cdf69787844aefffe86f50f7da5e09f2ab7c44a127f9db6977fe66ace016824ac36da5df7a22af2ee9ffd67db6977bf68aab2e27da07f6da5de854aa64f09ed2d6db597769d8a8ed3678f6336d65dc76baa08339da843db5976cb9ca756d6744beb6d65da115a9a3d79c7db1) (by decide+kernel)

private theorem _DYS:WideCovered band51 10829050 11860910:=PRB band51 Z1.f567 10829050 11860910 (WB 206367841368 16 0xf7a972dd8e43bfb7ad3eebbdea5ca9cb1093516b3d11bf7a97239db41233daca9a27dea5c6ace9007ff2b17bf8f7997125e53f82d9ac14597ce65c281acfaaf3eaf26d3f3997057703def44ab7f103ce65bff298f5743aacd1aff3996f48903d908daae9c73ce65b604fcfc6dceaa7c8af3996d48dd3c71cf6a547e38e25b60bc0bcaffca82766e3896d6e252ecaa529e48778de5b524a8b9e1e4a6fcd4e3796d23092e260e2999e2f8de5b3ee2cb74cc8a5d242) (by decide+kernel)

private theorem _DYT:WideCovered band51 11860911 13083856:=PRB band51 Z1.f564 11860911 13083856 (WB 240727612440 16 0x83ecb81ed15b9b3c71e93420f92df00e869e86bc67a3d83e4b776a6995857b153eae0f92dc97b8618b08c4251a81e4b6d7c21777b3b0bea1e0792da647c5a6170c1cff581e4b66767d5eda2b02958a0792d8ab0354f59ebf7ad17fe4b5ee9b14920eaf940f9ff72d72ed14fb405bd25ac7fdcb5a09113786e6efec69ff72d5c3314bdfdcbad0887ddcb53fbb92782e6e697d9f772d4b0a947f401b87b647dd4b504d2119a912dd4349f752d386b3453512b62640) (by decide+kernel)

private theorem _DYU:WideCovered band51 13083857 13542460:=PRB band51 Z1.f564 13083857 13542460 (WB 240727613464 6 0x21f72eda1034d11dc67521e43ee5d593fa8feec8cd79aa87dcba18689109a19989e310bc972faf720284df2c921a1792e3d62f3cc45fe4fcfa42f65c45e5873b9b7c8cf62) (by decide+kernel)
theorem covered51:WideCovered band51 (AX band51) (tail band51):=(_Q1 band51 8650677 8975521 13542460 _DYN (_Q1 band51 8975522 9281258 13542460 _DYO (_Q1 band51 9281259 9606103 13542460 _DYP (_Q1 band51 9606104 10217575 13542460 _DYQ (_Q1 band51 10217576 10829049 13542460 _DYR (_Q1 band51 10829050 11860910 13542460 _DYS (_Q1 band51 11860911 13083856 13542460 _DYT _DYU)))))))
def band52:Band:=⟨9,67,3249,4284,27464318551467050⟩

private theorem _DYV:WideCovered band52 8781748 8994097:=PRB band52 Z1.f2238 8781748 8994097 (WB 206367908984 16 0xc7199399c2d4fc3af7127a638e3327984c2ccd0b0e23c7231c664c8dd25db9c49c45330638cc7ef8b4a44bc0f885af7c7198f8b01d589fe3f106a898e331d210dac332c5e203e3f1c6637f38c6053247c3f4ed638cc5e9740c4dbc3e87c426c71988e5ebd9aa095b0f3ce58e33074614ad98c6121de2fb0c260cbd803f53c71c3a984e38cc2ecb3d916173b872d55c309977dca96fc3ec30e0f4386132e6e39ae085b0a1b87b70c265bd3c25c66940c35e1c5b6c6b5ce8c970ea38869684) (by decide+kernel)

private theorem _DYW:WideCovered band52 8994098 9302969:=PRB band52 Z1.f2239 8994098 9302969 (WB 1306953278584 16 0xe5ca6081db5092331bc6f9dcf26530427880481d5da36a143972981fccb02454d0d1ab9d0c58cc1246a010b521d8d117f62c6609184c085765ac6630bb163304865e042a25f631eab98b19823fd04214cdfb185e8dc18cc11e45010a0c4d8be3dde1c2608e431084dac2c5cc3ab2653244a60af1840d22d343193298f91a29792fe67160348c994c51b31aa6993228ab63b62c6656516d521acd4453569b16332f49192debd846287da98b19947742d46066c113a804c58cc9d1134a169448898899) (by decide+kernel)

private theorem _DYX:WideCovered band52 9302970 9631146:=PRB band52 Z1.f2240 9302970 9631146 (WB 1306953177176 16 0x66ce64e28b242f07e4bd6a99b39939d66925766925ed866ce64e02ca48a7ca484dc19b3993622a91ffaa91c80766ce64d05ea4764da45f27d9b39931a9e91db9691313666ce64bcd2247187a4397399b3992c8d091b1f2909a65e4ce64a678a4696fa413bf7972992657c91a32a900394e5ca648a8f246b38a3ee0b3972991daf69207268f6cc3e5ca646253a48ee5a3c856f97299127ae928d968ed5f3e5ca643324249f3463a2a2f9729906e509281b88e3f21) (by decide+kernel)

private theorem _DYY:WideCovered band52 9631147 10248889:=PRB band52 Z1.f2241 9631147 10248889 (WB 1305879435352 16 0x6daccb61605253f3ce315cb6d665a5a3a8f6f7e6f2fa1aeb32cd0a14622f7366a2ed75996311ea2a2579a9e456baccafd9a50f145cd03ba35d6656e78a859b7e65c28daeb32ae13941d18f31b3a4d759952296a044739843026bacca5351502ec1cbd618b5d66517a5280106e5c5581aeb327f7fd3fde072cfd1cd759927d40a2715b95e7beebacc821a452de454aa876f4d264b2bfa74f73652e873a693232d8d3e2593284696cf3993ca58913ffc938c7b) (by decide+kernel)

private theorem _DYZ:WideCovered band52 10248890 10866632:=PRB band52 Z1.f562 10248890 10866632 (WB 206367807512 16 0xe3799a5840b524d2973f237de66807cacf360a538f7df7999d620b2b0d292889b7de666d65ac5467a40b55df7999969eafeb228dd2137da6659422bbab4a2ddb2df69991878add4b6891b877da6632b52b3423a1b011df69987bf0abe21e8465036da661225aab210a0826fdb699824cea9efb67fae7b6da66009e2a33fc9f54cedb6997e114a7a8ce7af7f36da65ed7f29b6a69e272bdb5997650ea605c676416b6d665c368294ca79cf98a) (by decide+kernel)

private theorem _DZA:WideCovered band52 10866633 11947683:=PRB band52 Z1.f567 10866633 11947683 (WB 1305879469144 16 0x7ddcc9f836a25d1156c9d46f7a99350f64373fbad48405ef5325c45284754559f9afbdea64a87b9031a5ab2c5bd7bd4c90e269ff7a35633036f7a9918c973f3925ac1a9e5ef5321d1907d5087579e6bbce6641c468f7573aae0f3579ccc7f3c51ede9e559c326f7998ee9dd3e589faaecfc5ef53195872806f04554327fcea626fc91022739a958ad71c4c6d8309751ba1505618e3898da01f2e39a529e50edc6f31af2dc5bc9fe537eb4b8de6355630b678eca66699) (by decide+kernel)

private theorem _DZB:WideCovered band52 11947684 13183170:=PRB band52 Z1.f564 11947684 13183170 (WB 240727612440 16 0x85ecc8dd149d2c13324a30a17b321bfc36f89a7c7fb1f83ecc7fec95a8cbdb1b35fa0fb31eb441659f30c59fdc83ecc760f2d8791d311c8ea07b31c30e35dfdc9c3449881ecc6c15ad6a8d7f085bde07931a4e82579629c0e95581e4c65896d54012afeeec9ff93185ec45228c8be8e107fe4c5e7c113ee92af581bdff9317120e4d9f33bc32cc7fdcc5906d12dcf8eec14adf7731585e549a1edb9d7897ddcc5435c11f693ee2a7a1f773149e87465551b77c45) (by decide+kernel)

private theorem _DZC:WideCovered band52 13183171 13723695:=PRB band52 Z1.f2242 13183171 13723695 (WB 240727614552 7 0x25ed325e6e547dbf06d1682f95f4cd378c0f8a3c7740ea361fb32fd9e727480a4cf0ceb87f4cb1ca8c9288883377d2a1fb32a0b2f227d65cccb1a785f4c9d877c81b95932e101a17d3251d251eb2224ca5664) (by decide+kernel)
theorem covered52:WideCovered band52 (AX band52) (tail band52):=(_Q1 band52 8781748 8994097 13723695 _DYV (_Q1 band52 8994098 9302969 13723695 _DYW (_Q1 band52 9302970 9631146 13723695 _DYX (_Q1 band52 9631147 10248889 13723695 _DYY (_Q1 band52 10248890 10866632 13723695 _DYZ (_Q1 band52 10866633 11947683 13723695 _DZA (_Q1 band52 11947684 13183170 13723695 _DZB _DZC)))))))
def band53:Band:=⟨9,68,3192,4252,27260142535712999⟩

private theorem _DZD:WideCovered band53 8912819 9185825:=PRB band53 Z1.f2243 8912819 9185825 (WB 206367908984 16 0xcb29b5dab7d644d8fb18544396536ab2d9adbab7362f77d72ca6cde5ee595bfea45c8e46594d8b88b4b136cc38b459ccb29ac13a89221c73515f2df96535468f92aec2e6a2ab50f1c66d7f9ba50bd5fcc5308b638cdaa10509f7cfd98a14eac719b54712147e3d5313917b8e336958aea93041e625f2471c66d07c7953cad30c49832638cda35626b49381988e438c719b0f2c99383d5e11130178e3360881ba74dcb4221c7d71c66bff77b52171e44425efe38cd7d977aae478f88825c8) (by decide+kernel)

private theorem _DZE:WideCovered band53 9185826 9497831:=PRB band53 Z1.f2244 9185826 9497831 (WB 2406464906360 16 0x73e7344479504a10dfe43b39dcf9cd110108127097690a0bb73e734433d58498d256415238cd9cd1187e21209eec900862b2e734416e80492a4b23ef0d4c994d1305c810ba13b8f70097163344bb84042c662e3c8f71c58cd12d36410ac3438ed7b03163344adbe0429c66e3a2e10c58cd12988610a254b8e3f5831633449deb84277eee37ccacc58cd1258f61094ebb8da6ff3367351e809aeb7490a356b48cd9cd04d0a992c1b598d0ea6326536c31cd2a1b98023309e4c994dafdfc0ac966d08c764d) (by decide+kernel)

private theorem _DZF:WideCovered band53 9497832 9887840:=PRB band53 Z1.f2245 9497832 9887840 (WB 1306953177176 16 0xead66c9912285759e5b8183ab59b199d8a0e58696480768ce6d20a3a46328656bebda339b44b1a910c6595175668d26d160024b417251fbf5a349b4344292b2b89432d168d26d0471a49bdc24f9a939b49b3e838925bb0939a78e7ce6ceea12493f524d392f9f39b387ac924dec93021fe7ce6cd3a1a495f324ad7cb9f39b316429238149269c6e7ce6cb368a4965324876679f39b2771c92986c91d16de7ce6c83aea4be6224615039f39b1971e938aa0913913) (by decide+kernel)

private theorem _DZG:WideCovered band53 9887841 10511854:=PRB band53 Z1.f2246 9887841 10511854 (WB 1305879435320 16 0x6fb4dc49ef53e40ba065ee6fb4dc1b6a53675d9fcd956fb4dc046e530ec39f353d6db4dbedb75292439e9ce46db4dbd456523e6f9e048b6db4dbb8e151ef779d6c326db4db9ec35172d19cd3d96db4db7e37512b419c3b806db4db5c6850c86b9ba3276dacdb26ea50979f9b0ace6dacdb001c5084e19a72756dacdad7175050b799da1c6dacdaa0715063639941c36dacda5a8c5099bb98a96aebacda09af50b6d3981112ebacd9c1b35028569778b9) (by decide+kernel)

private theorem _DZH:WideCovered band53 10511855 11135868:=PRB band53 Z1.f479 10511855 11135868 (WB 206367807512 16 0xe789bc8074ba7caaa7adf39e26f095bae3f8fa95323e789bbd084b7b926a2eb2f8e26ee0c32d9ceca82272e389bb5d0eb4eb1a9e28678e26ece4eace7c9a6f1c0e389bb0fbeb232e299659f8de6eb059ac45e3a5c10ee379ba7380b0152e94a2d78de6e8620abb5aaa4905ce379b9d2a6add4b68fe00f7de6e6b12ab34eaa35faadf79b986c6ab8abe8b1d477de6e583faaa140a22ef8df79b932d0a941be865a837da6e397aaa2082a0fe47) (by decide+kernel)

private theorem _DZI:WideCovered band53 11135869 12344895:=PRB band53 Z1.f2247 11135869 12344895 (WB 1305879469144 16 0x7fe4db87bc25cd8ad78bc7effc9b69e1849ac44aecb639ff936be7289056135cfe6e3eee6d4cff11a08aab8cc2a7ddcda4b5a2270a656f36f0fbb9b450d54351dfad9ab19f7736793ca84e7295a9d0a3eee6cc87f10575eeb409637bdcd93400202d47565b162f7a9b20e233f6e83ac6a001ef536362887d99cd583ba73dea6c48660facaceaf469c7bd4d822ed9f62efd5c2bd5f7a9ad6dbc4172342b394e1ef535be80a7b45ced5da4339e26b9a030bbc104aa83d5) (by decide+kernel)

private theorem _DZJ:WideCovered band53 12344896 13592923:=PRB band53 Z1.f481 12344896 13592923 (WB 240727613464 16 0x89f4dbebc4d2c98b79ed2b70fe9b63303a3206b738e2aa1fd3698a3341cec16683fc43fa6ceb3ba7c7033cbd74685f4d955258ed20d9954d290be9b19fbf1c20d9325d78a17d361c6213595e8e4229842fa6c0600666a0d8c7147f83f4d7ad388c4e5c58bc79b07d9aecc8597a9a1f12cc720fb35c803f2da07be1c13540f66b6af5e58155dc251b881ecd68cdc4aa098582420d03d9acd40d14a1486ffc152079358c03a2813a95f5fd13ff26afb1364ddb2cbd8ef1) (by decide+kernel)

private theorem _DZK:WideCovered band53 13592924 13904930:=PRB band53 Z1.f2248 13592924 13904930 (WB 240727614552 4 0x97d4d734604da72fef50b08a5f93478050350deded2fb7097fcdb9604519e01d7472afa27d3731b152820d7cd09a0d) (by decide+kernel)
theorem covered53:WideCovered band53 (AX band53) (tail band53):=(_Q1 band53 8912819 9185825 13904930 _DZD (_Q1 band53 9185826 9497831 13904930 _DZE (_Q1 band53 9497832 9887840 13904930 _DZF (_Q1 band53 9887841 10511854 13904930 _DZG (_Q1 band53 10511855 11135868 13904930 _DZH (_Q1 band53 11135869 12344895 13904930 _DZI (_Q1 band53 12344896 13592923 13904930 _DZJ _DZK)))))))
def band54:Band:=⟨9,69,3111,4219,27397671992703663⟩

private theorem _DZL:WideCovered band54 9043890 9319639:=PRB band54 Z1.f2249 9043890 9319639 (WB 206367909016 16 0xcf39d359091607de888e34d7cf39d1c7cc971a3f078de7e7cf39ce1edd1732e5e68d9af6cf39c86825d8514a158d4e06cb29d77dc35490f9108d0115cb29d780b2d51b82108cb425cb29d6d47dd52af4608c6734cb29d6fbc2163383a48c1a44cb29d5b18b162261638bcd53cb29d2f1a254de8e228b8063cb29d234e8168b0b928b3372cb29cc742f12d33f118ae682cb29c91b7350546c508a9991cb29c767861170d5a08a731acb29c475cfd2495d608a4ca1cb29c0527df55e6ba08a2629) (by decide+kernel)

private theorem _DZM:WideCovered band54 9319640 9634781:=PRB band54 Z1.f2250 9319640 9634781 (WB 2407538648184 16 0x74749c24acdc249e72d2607bae8e9384586e049fa85a4adbb5cdce7092dd40908d2ec934fe59d9ce105ecc12818ad921d0c32329c285fa021442a923a036646538504e4842669d2460cacc8ca709f982084ad42489b1d19194e13d368108d72490e94a32329c2761ec210d0c92138b46465384e518842098f2413da8c8ca709c1da083d45648013c9a1a4e3ce389b45853b8fb58933339ccc0d90bb579551ed1306667397807c964d15463c6ea0ccce7500f704ed3e4447675b9999ce9d09a2a42cbb88e81c7) (by decide+kernel)

private theorem _DZN:WideCovered band54 9634782 9989316:=PRB band54 Z1.f2251 9634782 9989316 (WB 1306953177176 16 0x6ad2757f9e24447da61b311ab49d5bf7890b6d297d2e46ad67572a424ab0d65ce40fa359d5a5c0926fb596ec13e9d2755ea3a4989d65a7c8ba349d54fee922e7d965232e8d275470f248c646581507a349d4e934920a1595b851e8d2752a3d24892a655ad83a349d468fe921175951e70e8d2750834a4828765345ffa749d3cd6c9260d594848fe9d274e1b1a4a203650de7ba749d30ddc93364d93eaaee9d274a56d24f04864e76f7a749d20ba8944e409350cd) (by decide+kernel)

private theorem _DZO:WideCovered band54 9989317 10619601:=PRB band54 Z1.f2252 9989317 10619601 (WB 1305879435352 16 0x6fbcecf4c85335bfd10568b7de766d59a965a1e85c3c5bef3b2fd81498aaf41ae20df79d944f8a3f7e7a03d2f6fbcec839a51975bcfd1a737de762f6aa89de1e7c25b5bed3b09a4d440c6f3cdf18df69d806baa1663b9dd5ab6fb4ebdc06507fffce9de537da75d6dfa83349e7287a9bed3add9994184ff381013db69d662d8a0f2eb9b6e28edb4ead6c250bf61cd6a23f6da752d31289eada68e99fb6d3a7e44542ad7333410ddb69d4097c9eea149906a5) (by decide+kernel)

private theorem _DZP:WideCovered band54 10619602 11249885:=PRB band54 Z1.f483 10619602 11249885 (WB 206367807512 16 0xeb99de0842b956ceaea3779e677715badee05ab0efde799dd9910b63322a9d4739e6775b992d2ec4a9db3be789dd29a6b373fea5056b9e27734ac2c9343a8a77ae789dc7834b126fea036679e277065fac005ba773b8e389dbe352aed0929b675f8e276edb82b5b7ea63ff7e389db8b72ac40e696985b8e276d81f2ac3fea50c35e379db1418aa1d5691c9538de76aebfaa4f8ba3d874e379da5bf6a862ce8cfa4f8de7686bfa9e2c9a2a4b2) (by decide+kernel)

private theorem _DZQ:WideCovered band54 11249886 12431669:=PRB band54 Z1.f2253 11249886 12431669 (WB 240727579736 16 0x81ecec593425af79d7b626b03c9d7e042499c31af1f5cdff93ae11188fd39d5da4d8bff275ac05d17865aba15ef7fe4eb0763224f1b571c45cffc9d55e69437924adeb9b1f773a906e68419475b3d55beee7509e7d044316b546e97ddce9e829201b1f5682650fbb9d364373f92dfacb7d99f773a51ba67de60f58d5d23eee7469bd8fc77a6b077e37ddce8145d9fde5b95e8844fbb9cf2e133e30dd6b84181d7339eca565e180c566e4fbae673cd5b0bac3c0ac42be) (by decide+kernel)

private theorem _DZR:WideCovered band54 12431670 13692238:=PRB band54 Z1.f486 12431670 13692238 (WB 240727613464 16 0x89fcecd1b752f367ba1da9d13f9d80b97a3602e73ee63227f3ad219e42ab51e742e5c3fe754d0e87ddffdcd520987fce9fcc10eca78d983c910ff9d304e11c33a032baa1a17f3a4252c35dee2e4db62c2fa744af6466f94dc8830385f4e83feacc485118e9e850be9cfce7817aaa6f186e020fd39e45052d9f05e273df41fa73a52d45785e4c3b3fc83ece70bf2ca9a9f185007707d9cd93809494d8b0531e607b39a1f7427f45b600c5c40f673305a84d34c2bee4f6) (by decide+kernel)

private theorem _DZS:WideCovered band54 13692239 14086165:=PRB band54 Z1.f2254 13692239 14086165 (WB 240761168984 5 0x4c7d3ab9eec2f2d60bd6f0159ae6741457f9cc81c7ab78a92e04eb5ef5d0c861eb52224a5c29df73ac2079a58e9aa68c57f3b7d6852918fe0d2210f) (by decide+kernel)
theorem covered54:WideCovered band54 (AX band54) (tail band54):=(_Q1 band54 9043890 9319639 14086165 _DZL (_Q1 band54 9319640 9634781 14086165 _DZM (_Q1 band54 9634782 9989316 14086165 _DZN (_Q1 band54 9989317 10619601 14086165 _DZO (_Q1 band54 10619602 11249885 14086165 _DZP (_Q1 band54 11249886 12431669 14086165 _DZQ (_Q1 band54 12431670 13692238 14086165 _DZR _DZS)))))))
def band55:Band:=⟨9,70,3069,4181,27551407663592621⟩

private theorem _DZT:WideCovered band55 9174961 9453454:=PRB band55 Z1.f2255 9174961 9453454 (WB 206367909016 16 0xcf39ed9476184e1909903f8ecf39ec3004d8547c188ff1dacf39e09904bb5518678fa425cf39e5c0323bb5ce868f5671cb29f46d25530ee7858f08bccb29f681b51609f7d48ebb08cb29f49867d58900748e6d53cb29f27337d539b0248e1f9fcb29f085a696248e138dd1eacb29eccd0a96e9f4a38d8436cb29e608d0d94b7f738d3681cb29f3b9a0d13265728ce8cdcb29f2c8d2509c50518c9b18cb29f2722c908e93d18c743fcb29f2618290c711518c4d64cb29f236df90f1aa308c268a) (by decide+kernel)

private theorem _DZU:WideCovered band55 9453455 9771731:=PRB band55 Z1.f2256 9453455 9771731 (WB 2407538648216 16 0xb4b49e223c3025d286a951ad374749e25f98024838b994cd1f74749e26d35c23deba8947f6a74749e26191023f7c789431b674749e2509cc242b41793e40133339e2921b4213818693964d33339e28fea42128b7693489833339e28c95c211dc3692fae433339e289128211592592ad3033339e285500210dfc5925f7c33339e28160021050659211c734349f31d33524b5df491c41334349f244c6526e3ad391765f34349f448c4d5f11a029128ab33339f3a9c796c4c46190daf633339f2aacad6e68e80908d42) (by decide+kernel)

private theorem _DZV:WideCovered band55 9771732 10129793:=PRB band55 Z1.f2257 9771732 10129793 (WB 2406464804984 16 0xb66f3e4f36546786d9a9181356b3ec89c1223fd499f619356b3ec8da926c443995ab0356b3ec3b25264dc3990cfc356b3ebe26925de6b98bf47356b3eb81fd2583e2987193356b3eb24bd2563e29823de356b3eae16d251b9297d62a356b3ea952124e5a2978875356b3ea52d1248239973ac1356b3e9ee01247cd996ed0d356b3e9729924a501969f59356b3e8d57d2510899651a4356b3e7c6f1268f609603f0356b3e67f8d2850b095b63bb4eb3e465892bb700956887) (by decide+kernel)

private theorem _DZW:WideCovered band55 10129794 10766348:=PRB band55 Z1.f2258 10129794 10766348 (WB 1305879435416 16 0x71c4fd5fb853f3233489018e389fa8a60a6fad228eb291c713f488a94be443d1889db8de7e771ba94d627a275d271bcfcbf535257fed43b4d4e379f93f22a406c9a84fc05c6f3f1f945468a82d051cc38de7e2c6d28ac365a0082f71bcfc2c8551379093ed98cdf79f7f674a2097527b4579bef3ef073d436b21cf1afab7de7db7dd2886ec39d9a8c6fbcfb1305511200539fe47df79f5423ea318dca718ef3bef3e6bec94c93d0cde429f7de7ca47fa969f909b2cea) (by decide+kernel)

private theorem _DZX:WideCovered band55 10766349 11402902:=PRB band55 Z1.f2259 10766349 11402902 (WB 206367807640 16 0xeba9ff10f4bba64e2b7fa5baea7fb84d2e7d7f8ad632eeb99fea2bcb8921deb31f1bae67f9019adc8d86ac2c5deb99fdde4ab5c92daae43d3ae67f5fc6ad25c15aaf58ce799fd3820b33b696a9688f9e67f425b2c70b74a9bebae799fcdc72b0a7e12a48d479e67f2beaabc8e73a887e9e789fc578aae0b7ce9fb2039e27effd2ab48692a75118e789fb9b30ac1220a9ad6bf9e27ed5abaaba371a61a47e389fb2522a9d854695fb7b8e27ebcb52a3dd70a4e375) (by decide+kernel)

private theorem _DZY:WideCovered band55 11402903 12596444:=PRB band55 Z1.f2260 11402903 12596444 (WB 240727579800 16 0x83ecfcfd1ea71ea5f601a6e40f67e3eda1304d1f6fbf82a07b3f0fa6a93e79b97b8e7303d9f7d6c0486338bbc906781ecfb7bdaa3535855daccb3ff27d8adcd15522a6e88b11ff93eb6eac88339f171d7e6ffc9f5608f428bb87b7b5227fe4fa5ccaa0e9c035b3f28bff27cf7b990382a96d51dfdff93e6016a8126b0968215affc9f2279e40bc553b2d9db7fe4f886ea207d6d958d185bff27bd017105bf706c1b0e5df53df9c9a5f741215e6ad0eba9efa13e2f5a750ae99ff) (by decide+kernel)

private theorem _DZZ:WideCovered band55 12596445 13869554:=PRB band55 Z1.f2261 12596445 13869554 (WB 240761168024 16 0x8b027f3bdbca86b59fd3a1f28b027ebbe5c9c022eed26b208b027e444cc91ce30dd1344f89027dd34ba88323cccffd7d89027d7feea7fe068bcec6ac89027d31b5479568dacd8fdb87027ce1c6872a9249cc590a86fe7ca99f86d06638cb223886fe7c745b86883d17c9eb6784fe7c3aa3663d2486c8b49684fe7c083c65fd7745c77dc484fe7be5ad85be0794c646f284fa7bbe9e258df0c3c5102182fa7b984ba55fedc2c3d94f82fa7b7999652cd331c2a27f82fa7b5f2d25082b70c16bad) (by decide+kernel)

private theorem _EAA:WideCovered band55 13869555 14267400:=PRB band55 Z1.f2262 13869555 14267400 (WB 240761201784 5 0x135fcf78548c7372814d9b4089af67880161d4b9041ec3e9bcc853dd76a32c042a2b5d19965c39f4ca19d565ef13ac1f291604f7facdc5c7b340d4d8c2) (by decide+kernel)
theorem covered55:WideCovered band55 (AX band55) (tail band55):=(_Q1 band55 9174961 9453454 14267400 _DZT (_Q1 band55 9453455 9771731 14267400 _DZU (_Q1 band55 9771732 10129793 14267400 _DZV (_Q1 band55 10129794 10766348 14267400 _DZW (_Q1 band55 10766349 11402902 14267400 _DZX (_Q1 band55 11402903 12596444 14267400 _DZY (_Q1 band55 12596445 13869554 14267400 _DZZ _EAA)))))))
def band56:Band:=⟨9,71,3028,4074,27445653017084432⟩

private theorem _EAB:WideCovered band56 9306032 9587268:=PRB band56 Z1.f2263 9306032 9587268 (WB 206367908984 16 0xcf3a16e078157ae44b2494899e742b200a29dfc57647ef333ce84f8d7750a5f9248d6a9e79d09b2128a6930cc915edbcf2a17c595d42aecd72220c596542c5dff262184ce4307af2ca854bc6f49ee1a1c839b965950a4526291ee4329024facb2a1317c2d1523c351fad03965424f6712269fdc63e20272ca8463d01438d018c79cc865950814d3281a64218eeb18cb2a140a0914a77ae11d393f9654268bb928f1260239d5932ca84bd2f25373c1c472713e595090dbe4a665fe08e26eb) (by decide+kernel)

private theorem _EAC:WideCovered band56 9587269 9908680:=PRB band56 Z1.f2264 9587269 9908680 (WB 1306953278616 16 0xebd68092297093d7eb25cc723af5a023e04424dba7b96e351ebd6808eaed092c3caa5a5363ab5a02462b0242a4f9964660ebd6808ce3b09175f6257df9faf5a021773024b6ba795a96f68d2809c5240852a8da556bd9a34a026dd84213fd95950c7ee6d2809a8db084cfa5652f81b9b3a02666f02127cf4946f8ee6ce80988e40847f0d2508455ab4a12f9b1d684767393d29e6ad2843dae25b7dad4a4e1095a34a128b11915991619335ad66ce84d5469451d7f024b9cd19b3a1221899090a0609298bc) (by decide+kernel)

private theorem _EAD:WideCovered band56 9908681 10270270:=PRB band56 Z1.f2265 9908681 10270270 (WB 1306953177240 16 0xeede84e816a7e66699cb63e6cda85562da467ad89c194e6cda855b1b24f43379b7c5d6cda85534c24e92169b2de56cda854b54a4d7cf69adf6c6cda8542b824ccb959a90f46cda85392924c6a359a427b6cda852f47a4be0e499f4046cda85249fa4b6e8399a58b6cda851871a4b65e39957136cda850ba8a4b357299089aeada84fcb4a4b876298ba22ebd684ecbc24bb901986ba9ebd684dbcf24b98c1981d31ebd684c73ca4c4f1097ceb8ebd684ad9724dee10978040) (by decide+kernel)

private theorem _EAE:WideCovered band56 10270271 10913095:=PRB band56 Z1.f2266 10270271 10913095 (WB 1305879435416 16 0x73c50ce23854b6b9f4d0a8ee78a19661ca8a423a97a161cf143206a14f7ee6d2a5b3b9e286337aa9b5faca4ae7673c50c4a365310f7748230ae38a18568ca57632a8dd251c714302afd495c3cd16bd238e285f413a8f5ee8a23ab371c50bbe9451a8baf433b84e38a171b6aa2e605a840349c7142d69b544cca2d031f0b8e2859cb8a8790049fc6f171c50afdb651058473e5400e38a154bbea28714a7a3441c714268e714bbbe0cef80ff7de85087fa86e9609d532e) (by decide+kernel)

private theorem _EAF:WideCovered band56 10913096 11555920:=PRB band56 Z1.f2267 10913096 11555920 (WB 206367807640 16 0xefba1e3368be24f3ec15143bea87760baf2ed5eafb760efaa1d76debb3c476bc69c3bea8745812e74f1cae7d7febaa1cb5b0b86af2eb7823baea8722092daea1aad439eebaa1c5d3ab54b366b29ab7aea870cde2cf6158ac09bdeb9a1be27eb2b0c9eadb333ae686dfe5ac55276aacfdceb9a1b222ab037fd6a8cbafae686b4462bc7394a995fae79a1aa3d4ae0300ea3e42b9e6869db8ab26f42a85c1ae79a1a49c8ab7d7069efca79e6868723aa97380a72238) (by decide+kernel)

private theorem _EAG:WideCovered band56 11555921 12761219:=PRB band56 Z1.f2268 11555921 12761219 (WB 240727579800 16 0x83f50cce5b28a0637e15c41c1fa86390493bc6dbb05fa860fd4308c5099ac63b80898107ea175cb74acb36cbf0ade81ed0b4577249977ddee87f40f6857d50d1d102aaf25c7207b42b33a68bc9eb376ba7703da14d3d4448e048ba235a81ed0a0e76a1dc1bbdc74bcc0f684d04f50ba30dadebe61ff942596bc83f95eb6ceb6cffca1215ee4206944b53bd47fe5088a3ca108cb9da00fa40f6836ef5d168714acb2049df741e9a4860ee923631c64efba0f35032ff5730b0f141) (by decide+kernel)

private theorem _EAH:WideCovered band56 12761220 14046870:=PRB band56 Z1.f2269 12761220 14046870 (WB 240761168024 16 0x8d0687d84aebe2079fd656968d06872f10caecb29ed51cb48b068694f60a0dd2edd3e2d38b0686137f295059ccd2a8f28b0685b6cf28b920bbd16f1189068553cd882c46ead03530890285005407b75449cefb4f890284c03ba7487e88cdc16d89028482a6a6f3bda7cc878d8702844251869b4406cb4dab87028419e6e650cbc5ca13ca86fe83ebcc46133604c8d9e884fe83bc1c25d3eee3c7a00784fe839238659eaac2c6662684fe8378a38568aee1c52c4584fa8358154540c240c3f264) (by decide+kernel)

private theorem _EAI:WideCovered band56 14046871 14448635:=PRB band56 Z1.f2270 14046871 14448635 (WB 240761201784 5 0x13a0509e5e2ea0a6f5cdc77fb9d0284991975609711ed9f0d4c89424af92a404c16b6810e2644a15251693140f93b194b11a0d08b137869cbe48d79076) (by decide+kernel)
theorem covered56:WideCovered band56 (AX band56) (tail band56):=(_Q1 band56 9306032 9587268 14448635 _EAB (_Q1 band56 9587269 9908680 14448635 _EAC (_Q1 band56 9908681 10270270 14448635 _EAD (_Q1 band56 10270271 10913095 14448635 _EAE (_Q1 band56 10913096 11555920 14448635 _EAF (_Q1 band56 11555921 12761219 14448635 _EAG (_Q1 band56 12761220 14046870 14448635 _EAH _EAI)))))))
def band57:Band:=⟨9,72,2988,3631,27312432240417372⟩

private theorem _EAJ:WideCovered band57 9437103 9721082:=PRB band57 Z1.f2271 9437103 9721082 (WB 206367909016 16 0xd34a2f2c19547740ec9454fad34a2ec56d9424cd5b9405bfd34a2e368013a09a9b93b682d34a2d8fe3d300c1ca936746cf3a2bd2d18f494d39931809cf3a2b5651cebefd6892c8cdcf3a313d0016970607927990cf3a308b9f55d831f6922a54cf3a2fe884152e098591db18cf3a2f726094c2b9a5918bdccf3a2ee80714402584913c9fcf3a2e684cd3d0bd8390ed63cf3a30549d96a2b592909e26cf3a3018491679d452907689cf3a30560016ffa611904eeacf3a302e6d96fb394090274c) (by decide+kernel)

private theorem _EAK:WideCovered band57 9721083 10045630:=PRB band57 Z1.f2272 9721083 10045630 (WB 1306953278616 16 0xedda885522b094f01b26522fbb76a213f5d0258050b98f982edda884a6dc096c0faa62a917b36a2139bb425099f9985b0aedda8844b2909650926602f35b36a214f2882448c9897bc9168d28860b80085a8f1e5db551a34a21810a0215a466971e1868d2885fd170851eb965b3b71a34a217ce94213c985967fa068d2885ebec084a649258c191ab5a2f3b1d15d9ebd395e1286ad68bc9ebc58ca8bce5647adab5a2f788a57314cd29542af68d28c295f65832e34653cdc9a34a302707159419d094a436) (by decide+kernel)

private theorem _EAL:WideCovered band57 10045631 10410746:=PRB band57 Z1.f2273 10045631 10410746 (WB 1305879402648 16 0xf1c51ac788a476bb27b6bebc7146915228a767b9e3c836fbd1d288c94e7d2a767829bef474551a52b3c99d4ece6fbd1cff449482a2273fe45bef473a75a510e489cb0556fb51ccfec942345e718465bed472ccf25028969c11dd6fb51c9a8a93c48566f0a81bed471ddb24ee7f49b73646fb51c546893981126c909dbed4709b0a4e94c39ad4ebedb51bf0e093c50ca6a16bbb6d46f003a4eb6b19a3673edb51b739c93fd082679cdbb6d46c7efa50fab09997fa) (by decide+kernel)

private theorem _EAM:WideCovered band57 10410747 11059843:=PRB band57 Z1.f2274 10410747 11059843 (WB 206367807640 16 0xeb9a301078ab8653ea30a0fae68bf29a2aa30dea8240be79a2f9fe8a974bf69e164b9e68be2f62a16deca6e71ae79a2f74f8a7644ee9922879e68bd60ca9abcaaa5aa28e79a2f3e42a5c29a6942ebf9e28bbd45a943d38a46d37e78a2eaa7aa4b80de8f3afb9e28b944e2913c46a33046e78a2df120a3d2cd68a473b9e28b6b3ca8e74a4a1f355e78a2d5fa2a3602ce8553739e28b37d8a8fe992a0b665e78a2c3914a4b8a46805fb39e28ad389a9798a09f7973) (by decide+kernel)

private theorem _EAN:WideCovered band57 11059844 11708938:=PRB band57 Z1.f2275 11059844 11708938 (WB 206367807640 16 0xf3ba330b3ec170d3ecaa82bcee8cb2952ff355eb20b92efba3284eebe0fc76c5b467bee8c8f962f1727cb0cea1efba322c76bab402ec0c0a3bee8c8850ae487baaf91b0efaa31efaeb7a35e6bbcce3bea8c6d212d93cb8ae54bfefaa317b2cb5261deb6d91bbea8c4eb8acf4ef6ad17cfebaa30f4f6b264f96b1e55baea8c39f62c3c494abdaddebaa30db1aaf9468eacf193aea8c31712b9e0b2aa9dedeb9a308c64ad73986a7fdd3ae68c1347ab15f40a960fb) (by decide+kernel)

private theorem _EAO:WideCovered band57 11708939 12925994:=PRB band57 Z1.f2276 11708939 12925994 (WB 240727579800 16 0x85fd1848fe2a6159fe29e1542fe8c0db0947bd53b0ffce617f45f3cac9f706db85848f07ea2f0df64dcac4cc1855683f51738cea5c258de02432c1fa8b906a525e442afc2dd20fd45b9e22906fb137b9d0907ea2d4f4b46f17e8bc919281ed165aeea2c108bddaa5140f68b1d1b510a1f9ae85ec207b4587e38871d46b71b57f03da2bebf842fbee4b79dcd81ed15aa18a1788a9db306ec0f68a844a10f6710ad48fb1e794537f8e624d56367cdf6f3ba29a33030bae20b34883) (by decide+kernel)

private theorem _EAP:WideCovered band57 12925995 14224185:=PRB band57 Z1.f2277 12925995 14224185 (WB 240761168024 16 0x8f0a8da5bb6dbf6abfd90b398f0a8d15c5ac6e029ed7ce488d0a8c954aeb4162add691588d0a8c3cc94a5a8d2cd554668d0a8be7a489959c5bd417768b068b9f7848f037fad2da848b068b64300851d729d19d948b068b32b807e28418d060a389068b00380770f2e7cf23b289068ad53227124bf6cde6c189028ab50fe6b51955cca9cf89028a94d0e66fc404cb6cde87028a725fa625c843ca2fee87028a5e7245e69282c8f2fc87028a436ce5add5a1c7b60c84fe8a2c34e57fb150c6791a) (by decide+kernel)

private theorem _EAQ:WideCovered band57 14224186 14629870:=PRB band57 Z1.f2278 14224186 14629870 (WB 240761169016 5 0x9d0e8ec2882b1884c4df3bee9d0e8dd7830b1cfc73ddfefd9b168e0f048882f6c2dcc20c99168eb364e9c47089db851b8f0a8e5e6fa7c97ef0da482a) (by decide+kernel)
theorem covered57:WideCovered band57 (AX band57) (tail band57):=(_Q1 band57 9437103 9721082 14629870 _EAJ (_Q1 band57 9721083 10045630 14629870 _EAK (_Q1 band57 10045631 10410746 14629870 _EAL (_Q1 band57 10410747 11059843 14629870 _EAM (_Q1 band57 11059844 11708938 14629870 _EAN (_Q1 band57 11708939 12925994 14629870 _EAO (_Q1 band57 12925995 14224185 14629870 _EAP _EAQ)))))))
def band58:Band:=⟨10,46,4339,4772,8643342041892577⟩

private theorem _EAR:WideCovered band58 6029256 9208739:=PRB band58 Z1.f2279 6029256 9208739 (WB 206366726296 16 0xcaae25260be86dfe8c83a3c69e243743b3298d8b8b3ec69e25eb7392327c8a92d8bade26847b3bc33b899a72bade26b38b373afa891e3fbade2665a33352a988a20cbade26162b2f86d88825dabade25bbf32b1dd787a9a7bade25624b271346872d74b6de25079b23573586b141b6de2499631e6ee486350fb6de2431bb1a198385b8dc041e003aa807b452853ca9041e003aa007b3a284c076042e0018f002ba5182cfaa041e0018c802b7607b0c7d) (by decide+kernel)

private theorem _EAS:WideCovered band58 9208740 10098995:=PRB band58 Z1.f2280 9208740 10098995 (WB 206366727320 14 0x34af8dc77c923eefb343267a57c6bfdc481cc5c9920cdd2be34f0ca3a462dcc1433e75f19cc0d18cc76a5cc00b3af8c94ea8ad55932c6f399d7c6414544700d8953f37cebe31c7c21f0fa3ca2368e7571849250cc74da4d39b33ab8bd030856074b24ac0b9d5c5b9b44294514915da0ceae2b6ea2121f49c8329d67571404e50c6998a3db3573ab87c23c85d39a31ce8dd955c514aa3e0f4208d7c09) (by decide+kernel)
theorem covered58:WideCovered band58 (AX band58) (tail band58):=(_Q1 band58 6029256 9208739 10098995 _EAR _EAS)
def band59:Band:=⟨10,47,4255,4748,24419746187794235⟩

private theorem _EAT:WideCovered band59 6160327 9379001:=PRB band59 Z1.f2281 6160327 9379001 (WB 206366726328 18 0x32ab9bc678f3914a11e3973955ccbf377c416cf8e2144c6ae6b02939d1c274692e75f7736a5ad9f09a3630a962fbb9b39d6ce5f2d917593d7ddcd918f66b8f6b8b2ee3beee6c2143312e154558945d7735d95996539a628cdbaebb9ace78c9f0911136b6775bcd609c6456e678937f8bade6b538b1d94e3445d1f5d6f35818d8d4f41620f20eeb79a7582c26e1890f7d9175bcd2eeb60cc96487410e06ce41a45035c2f1c361a9835f2020dc03d0c0a1916601a7900a1e0115c430a9444083c803880055d807d6e76) (by decide+kernel)

private theorem _EAU:WideCovered band59 9379002 10280230:=PRB band59 Z1.f2282 9379002 10280230 (WB 206366760088 14 0xd6ce60628528a3cb673749b5b397ea70490402c9be1b0d2ce5efa0d203616e6b98ef4b39786b546cd89a99eac6d2ce5e440517adb2663bd434b39766d1450535897f3dbd2be5d037111b619e5be19b4af97111a43b59b695fcf0cebe5b54190b96a565405eb3af96949b42901a4940605cebe5a58f9078c70e4c2a3f3af96563241f4b12920f1acebe56cc8109b3086444e933af9602804118e5090182e) (by decide+kernel)
theorem covered59:WideCovered band59 (AX band59) (tail band59):=(_Q1 band59 6160327 9379001 10280230 _EAT _EAU)
def band60:Band:=⟨10,48,4174,4724,12291164072472397⟩

private theorem _EBK:WideCovered band60 6291398 9549263:=PRB band60 Z1.f2283 6291398 9549263 (WB 206366727320 27 0x69675731e10a6e8ae46d73f3afad3c7e78e7dd5216e959d7d6231d3c987898fb8c4c2feb391a1a0dfb4475d1f617f598fa0cf560de38ebf2fbfaca4a266f174f1b77737dfd64299332fda68d3c77beeeb1ed2996a242c65e9a5f775909e0ca1469630f7cafbbac6c7c6497749177d5f7ddd628ea320d5348b3f6cbeeeb0cdf98e23d1c560155f7757f104c46990a29039efbbabda4461baec513834b75dd5dcf9309f8f2894262baeeae5c6183025944618fdd77573554c041b0a210f72eb7abacf25f8ec250f893375bd5c9d22f97042874557badeade0f97b373143630a5d6f56b5b0bcdac0a191b4aeb7ab3b025e0c8450b8f1f75bd58c132ed586285484db6deabbd5174dad94264855b6f55b714b970fca11271c18ba03cea0361b430795080a5d003ef002a6907fd06f) (by decide+kernel)

private theorem _EBL:WideCovered band60 9549264 10461465:=PRB band60 Z1.f2284 9549264 10461465 (WB 206366760088 14 0xdadea575412e4f8767e84675b7a920524a32b9c9ea293d6dea3971923306ae76903b5b7a8dd2747abc6a9ca589d6cea2cb651b825a66e9c135b3a87d8945da1089aa87fd2cea10c4d134cf5e66a7eb4b3a80b40442261698ab75d2cea089a90c729d65eb3bb4b3a7f2aa42733b496ae69d2ce9f19e908bed0e56bf934b3a7860e41b90a294b15fd2ce9cc52d05ab5864ecb674b3a6b87e41ae08092b454) (by decide+kernel)
theorem covered60:WideCovered band60 (AX band60) (tail band60):=(_Q1 band60 6291398 9549263 10461465 _EBK _EBL)
def band61:Band:=⟨10,49,4096,4700,12366412977196781⟩

private theorem _EBM:WideCovered band61 6422469 9719524:=PRB band61 Z1.f2285 6422469 9719524 (WB 206366727288 38 0xd2cefcc9ea0a71a6944ee4d6cee289ba26363e934d4fcebefc6241debb4f924bbac30ef9cad9a2ecc6914a25c30ef93161a021a690c95ac2fef8ee699d46b6904890c2fef90f199a71768fc7c5c2fef89471982fe68f46fbc2fef81e819629368ec630c2fef7a2099411c68e4566c2fef7189991bece8dc49bbefef688298f61568d43d1befef5f5e98d26838cc306cadeee7651aa0cf58c423ccadee71131ac4a0c8b40a7beeef49d11824b438a3f11beeef4124980526b89be47baeef37db97e4f0b893d7cbaeef2e2517c648388bcb2baeef2af417ab7ab883be7badef2e049788a8387bb1dbadef2e11976866b873a52badef2630174f84386b988badef1db597367738638bdbadef1481971d31b85b7f3badef0a62970391b853728b6deeff1c16e97b384b65eb6deef61f96d43ab843593b6deef55c16bf1b383b4c9b6deef6f196a355b8333feb6ceef9d61685f2b82b333b6ceef373167162b823268b6ceee8e6166065381b19e067ec10a100d5dba8130d3061ec031d0021c61802f3e05eec02258014eb87e2c14041ec02288014da87a25bf041ec02240014c08721916) (by decide+kernel)

private theorem _EBN:WideCovered band61 9719525 10642700:=PRB band61 Z1.f1285 9719525 10642700 (WB 206366759960 14 0xdaeeea8db133877a8994336bbba57cd4b53c4a16377dadee93f9128c2a681878b6b7ba14a449025b9f604ddadee759f91f5736797ae35b7b993e046a81f9d5d23d6dee5cae915d4da716e3b5b7b9637a44bd649b59f9d6dee4b3f90fafde69618f5b7b8f0b84322c79956ced2cee2ac7d098b866154e74b3b863d1421cbe9753a4d2cee08eb906462259483b4b3b8049b41345d955079) (by decide+kernel)
theorem covered61:WideCovered band61 (AX band61) (tail band61):=(_Q1 band61 6422469 9719524 10642700 _EBM _EBN)
def band62:Band:=⟨10,50,4021,4675,9527833631363420⟩

private theorem _EBO:WideCovered band62 6553540 9456074:=PRB band62 Z1.f2286 6553540 9456074 (WB 1305878354040 38 0x61879e519d92be2c9049ca61879e39c18feeac8fc778617f9e48818d98448f4526617f9e0cd58b54348ec2d3617f9dce11898fa48e4081617f9d834d8752ac8dbe2f617f9d3495850b248d3bdc5f7f9ceb19833a948cb9895f7f9c9601810d338c37365f7f9c88a17e9c0b8bb4e45f779ca1417c11fb8b32925f779c78d17a83c38ab03f5f779c313578a6db8a2ded5f779be4f176c27389ab9a5f779b9d19755b338929485d779b44b973685b88a6f55d779aef2171ffcb8824a35d779ad08d6ff43b87a2505d779ae1ad6dd0ab871ffe5d6f9ae4b16c4d23869dab5d6f9ab6016a9963861b595d6f9a63c5691c6b8599065d6f9a13f16832738516b45d6f99aeb966b7938494615d6f993de5655beb84120f5d6f98cd416470cb838fbd5b6f98bd4962efe3830d6b5b6f988561625783828b185b6f98741960d6c38208c65b6f9869995f3efb8186735b6f9803095f1ed38104215b6797f2c15d876b8081ce5b679760e15cdd7b7fff7c5b679649855e41937f7d29db6f8f91a569bcb37efad70347804cd406da427e7884031f80128c014a397c6f3a020f801298014838744a12) (by decide+kernel)

private theorem _EBP:WideCovered band62 9456075 10356861:=PRB band62 Z1.f2287 9456075 10356861 (WB 206366760024 16 0xdaef29c501163d4c9e087ddaef28c7b112dc549d03d7d6df27aeb10fa4d09bff32d6df270b150b11989afa8ed6df270901083e7499f5e9d6df26250906a3d898f144d6df251ae505a9a097ec9fd6df23884903d1dc96e7fbd6df219a9905416895e356d6df1dd34106aee694deb0d2df20599cee3d3993da0bc70f1fcf78cf888892d566c70f1f8dfcce76ac925314c70f1f4160cd295c91d0c2c70f1ef1d0cbd6e4914e6fc30f1ea878cabd7c90cc1d) (by decide+kernel)

private theorem _EBQ:WideCovered band62 10356862 10823935:=PRB band62 Z1.f1288 10356862 10823935 (WB 206366759960 7 0x37bfcbf2614e7189a528ffdeef2f57b933a9f290916b7bbcb93984babb6a31fb5deef2d126d28b2b2886c436bbcafc8a48f2e1a1166bdaef2b31fd1ee6ba80471f6bbcaaeb14681379f0d22) (by decide+kernel)
theorem covered62:WideCovered band62 (AX band62) (tail band62):=(_Q1 band62 6553540 9456074 10823935 _EBO (_Q1 band62 9456075 10356861 10823935 _EBP _EBQ))
def band63:Band:=⟨10,51,3948,4650,25011225447126788⟩

private theorem _EBR:WideCovered band63 6684611 9351205:=PRB band63 Z1.f2288 6684611 9351205 (WB 1305878354040 40 0x617fbfd5e980f85f8eb025617fbfa2a97f50668e2c4b617fbf51957d28568da871617fbf06317b717e8d2496617fbeacc97946be8ca0bc5f7fbe55717775d68c1ce25f7fbdf88575b03e8b99075f7fbdf6dd7348e68b152d5f7fbdf9f971685e8a91535f77bdf3b56f990e8a0d785f77bda02d6dcd2689899e5f77bd51016c7ebe8905c45f77bcef5d6aa7568881e95f77bc8fcd6959fe87fe0f5d77bc25216812c6877a355d77bc01a1661d6e86f65a5d77bbec6964cfd68672805d77bbe41d632ffe85eea65d6fbbeaf1614ac6856acc5d6fbba9b560533e84e6f15d6fbb37215f00fe8463175d6fbac0f95e623683df3c5d6fba359d5de9c6835b625d6fb97b715cc15e82d7875d6fb905d95ca3fe8253ad5d6fb8ae615bba8681cfd35d6fb7e7c95c662e814bf95d6fb6a8555e1e5680c81e5d6fb52ab95f881e804444db6fb47e695c81757fc0695b67b806994933e47f3c8f5967b7bea5483fbc7eb8b45b67b7068148d3447e34da5b67b662994886dc7db100d967b448994bf33c7d2d26595fb6cd813c1ff37ca94b0327a12880199daa7c257102e7a02eb8039f917ba196027fa02ec4039e587a99e1020fa02e84039b18767b0e) (by decide+kernel)

private theorem _EBS:WideCovered band63 9351206 10060048:=PRB band63 Z1.f2289 9351206 10060048 (WB 206366760024 16 0xd6df668829044ce0998110d6df64a7a505943498795bdadf61b2710742809771a6daef5947c50e18e69669f1d2ff643f74eaae7d95623cc71f623b74ce5038945a88c71f61d8d4ccc8cc93d6adc71f619f24cb7b4c9352d3c70f61afa8c9e14892cef9c70f617794c8ca18924b1ec70f612ed0c7c12091c744c70f60d958c67ba891436ac70f608a38c56d8090bf8fc30f60359cc45304903bb5c30f5fd47cc305488fb7dbc30f5fc258c1e9508f3400) (by decide+kernel)

private theorem _EBT:WideCovered band63 10060049 11005170:=PRB band63 Z1.f1149 10060049 11005170 (WB 206366759960 14 0xe30f7623a540c47e9fb3cb8bfdd32a44e9989a6e53de2ff739a093532a69776237bfdc8bd94bbcbea4d5d4deff711c2528a4fe8f387f7bfdc1f3f48d2aba2c66adeff6f6dfd1f318e86fadb6bbdb910146bae6a0b701daef6cedd5163e167ebd336bbdb2997445f9f9ea797daef6bf2890dd456767f8b6bbdac1ff42f7a59c982edaef69c96909048a6e41e75b7da12fa419ca49a88c4) (by decide+kernel)
theorem covered63:WideCovered band63 (AX band63) (tail band63):=(_Q1 band63 6684611 9351205 11005170 _EBR (_Q1 band63 9351206 10060048 11005170 _EBS _EBT))
end
end AY

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AY
open AI AP AN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def band64:Band:=⟨10,52,3878,4625,10167559511965064⟩

private theorem _EBU:WideCovered band64 6815682 9069336:=PRB band64 Z1.f1146 6815682 9069336 (WB 206366726264 37 0x5f7fdfc8ed6b11a38a6318beefbf83ead23e4713bb6d7ddf7db8e59efaae25614efbbef89d4b330f5c469785f77deb085650893884d8ebeefbc853ac766870f90597ddf771b2589884e1d0b2aebbeed1aab02ec9c35eb3dd77dd86855efcfb863805baefbad2babb3e070b654775df75318570fe4e14b506eb7ee983aad6d65c253ef5d6fdcc8fd5a07b384227cbadfb8791ab2eec7073a3575bf6e50756449ee0c5ee2eb7ed5b1eabfb9dc1492b5d6fda258d580333820cf4badfb2b792b12197030f2575bf60a6c5680bae0408beeb7eb7e9eace4d3c03e66db67d9e1a94581d67ff76bb6cfb2e9c28aa55cfee4136d9f63bc6514f659fbb29adb3ec31b2a268d73f33a25b67d739a9462dce7de1e2b2bfb1edfa6fd03afab901657f6114b4dfb1d5f35c76cafebd7ba9c249ebe28ddd95fd77c5532b2a47bcc59b2bfad107a67c3b8f68def657f54f274d56991eb0652bafec2c469ac119bd1e19575fd8056935961b79f981aebfafa71a6aaba6f36d9e0bdf015dd01ac269e5d07816be018c801ca30bc98b682ffc01e9c02078878ac0a) (by decide+kernel)

private theorem _EBV:WideCovered band64 9069337 9615677:=PRB band64 Z1.f1147 9069337 9615677 (WB 206366758968 16 0xc70fa3bfdd8d686e4ae4f71c3e8e63862be559233dac70fa347b988d6f646b9df1c3e8ba20618e53912915c70fa28fe584092e428ecf0c3e88cac60747d901e51c30fa1d4457fc1da3e63bb0c3e86ded5f5b648f138cc30fa1c5797a860a3a38ab0bfe8652c5e22568e08c8c2ffa1443576c2fa360d970bfe83bcd5d3ebe8cfe03c2ffa094ad732f8a31e2870bfe80cdc5c57e68bf33fbeff9fc9ed6f88e22db772fbfe7f0ce5b55e08ae87a) (by decide+kernel)

private theorem _EBW:WideCovered band64 9615678 10571772:=PRB band64 Z1.f1148 9615678 10571772 (WB 206366760024 16 0xdeffb21e7119a074a14ffcdaffb0de3d15b444a04538daefaf7fcd11ea089f3a73daefaeea2d0e42289e2fafdaefae8c5509da749d24eadaefad6d7d07b7949c1a26daefac23990619449b0f61daefaa8ce105496c9a049cdaffa7ffed038c2c98f9d8daffa452e9066b4897ef13daffa0776d04eace96e44fd2ffa4c314ec7dd195d98acb1fa4bf08cc0af894cec6c71fa460f4cabd9c944963c71fa3fef4c96b7493c401c71fa3bc14c81388933e9f) (by decide+kernel)

private theorem _EBX:WideCovered band64 10571773 11186405:=PRB band64 Z1.f1149 10571773 11186405 (WB 206366759960 9 0x39c3ef7016547a2eaab0e5e30fbc02094a1e6ea698838c3ee8a13507e3da89b5ce30fb9687d3ad1be9e425f8c3ee03b84d49bca685d3e30fb6850d2eb60e95ec3b7bfed42504a3a86a4704adeffb415cd2363528d96177bfecdf1147aee4a25ac1) (by decide+kernel)
theorem covered64:WideCovered band64 (AX band64) (tail band64):=(_Q1 band64 6815682 9069336 11186405 _EBU (_Q1 band64 9069337 9615677 11186405 _EBV (_Q1 band64 9615678 10571772 11186405 _EBW _EBX)))
def band65:Band:=⟨10,53,3810,4599,10486803387575704⟩

private theorem _EBY:WideCovered band65 6946753 8949967:=PRB band65 Z1.f1150 6946753 8949967 (WB 1306952128664 44 0x5ebbf8191e578e1ef11219ebd77effae8ae80d9e2027917aefdf79cd5bd28bc3c17d2f5dfbdd8aab558a786fc105ebbf7941d567d2ef0cea4cbd77eef84cacad4de17b8f17aefdd9e99587c33c2b3a92f5dfba767aaf811784e0675cbbf72f1955cecef08b2fab977ee072cab892de0f4a4f72efdb0405579e23c1a5d4ee5dfb232b2b3c73782c4bfdcbbf5aad856d1e8b047baab56fee1648a15e88e06dbad6adfdbd4a141e699c098002d5bfb6c43a826eb380a9165ab7f6ae9950377a7004458b56fecbe66a0c85cdfe6d0b6adfd3d02d4badd9bf8a2c2c59fb50f7a67cf397e8d6e58b3f67e654cf1032fc0d08b167ec55249ad4ae5f5fe6b62cfd6ab2d38472cbe7c57ac57fb1e1da5898f87c71c558aff60f8c4b342b0f7d5b6b167ec8de89a59c1ded8fc75acfd8b36d34d48bbd903e6bd7fb061fa6a4ad77add06d7aff5e1a14d7058ef53323af5feb4cc89b6e2dde958735ebfd55d8d385c633d0953ebd7fa9aeaa6e63f579cf32d7aff4f6f54de1608f3177aa957eca8e49245a8de5212152afd92719243729bc8269aa55fb1ef0a47d13378c15e54abf6306b48e8666f0fbd2a957ec41c691b2a4de0e9d152afd839ed2338d9bbfb7faa55fafbed2464b4377b38a54abf5da6148cfa86eee02a0517e02df6034eb49dcb28009bfc03420038950bb52da8107f802cc00277c0726e63) (by decide+kernel)

private theorem _EBZ:WideCovered band65 8949968 9502578:=PRB band65 Z1.f1151 8949968 9502578 (WB 206366758936 16 0xc70fe46b297c29ac87fb96387f2062abd093a41e2231c3f8ea0b5dfd0b1fe33d861fc67b52eb9988f6ab4c30fe2dba9741924771e4e187f16936b8f5be39737f0c3f8b4075be72b1babeb85ffc56a42daec08d4f0bc2ffe258fd6bc5a466410e17ff0fb30b5097e3104df0bff862f15a171d17749985ffc22e6acd3fd8b3361beffe0b971654a8c5563bdf7ff04fd6b1db9a289636fbff82392587985133d477dffc10532c003e8917b9) (by decide+kernel)

private theorem _ECA:WideCovered band65 9502579 10262418:=PRB band65 Z1.f1152 9502579 10262418 (WB 206366760024 16 0xdb0fee04950675919c9792db0fed4db1046a7d9b89bddb0febdd6103a3719a7be9db0fe72a6d0704f1996e15d70fea8314ea9d3e986040d70fe90354e9e59697526ccb2fe72d2cca5751964498cb1fe70944c8e86595bdadcb1fe6ac38c7add99536c3cb1fe65788c6ab8994afd9cb1fe5f3e4c56c859428efc71fe58bd8c428f193a205c71fe51e8cc2dfa5931b1bc71fe4f620c18f11929431c71fe4f5d0c0350d920d46c70fe4c590bf1dd891865c) (by decide+kernel)

private theorem _ECB:WideCovered band65 10262419 11367640:=PRB band65 Z1.f1153 10262419 11367640 (WB 206366792728 16 0xeb1fe22d52ae3e415ae9b1ce3fc22fb5535276b19c0f9c7f8159ea9468ad5ac97f38fefd31a50df7daa4b5be71fdecfb29e673b527b0dc61fbbd32135c5eea0becb8c3f74bbaa5d7015390ef7187ee67d94a4751a61409e30fdc224e922fc94a0c6bbe1fb6b9e91f175a8fe1877bff6a240a339b65175466f7fed386345344fa1dcb8deffd9f70288d669419dc9bdffb290610e143e7f043f7c3f621212154f8cf599ded87ebd0a641e4519da567) (by decide+kernel)
theorem covered65:WideCovered band65 (AX band65) (tail band65):=(_Q1 band65 6946753 8949967 11367640 _EBY (_Q1 band65 8949968 9502578 11367640 _EBZ (_Q1 band65 9502579 10262418 11367640 _ECA _ECB)))
def band66:Band:=⟨10,54,3745,4573,16505064237381753⟩

private theorem _ECC:WideCovered band66 7077824 8824327:=PRB band66 Z1.f1154 7077824 8824327 (WB 206367876248 23 0x17df007e9aa0aab53261a981efba00f97bc15422bcc30ecadf7401e43f02a72bc9859523bee803abfc855139930a19637df006b6960abf92261210fefba00e0f72151461c41fde6df7401ab8f02a5153883735bbad803ac5804fc2bef05d5d375b00737c509f9695e0989deeb600e30ae13eb3a3c0ed02dd6c01bbc9827cffc7815193bad8034c6d0501b32f019243659038fef74710939a0102bacb20455ca853fd0ab3fdc1e5b63e21257031618457f2fcab2b7622ad082e8c728fa1c055d7005aaca07396d0debb0eabae00a5f840df8439bcedab575c012ca641d1780378ca72aaa801882181f9fe24ef731d553002c92503dbf689daa2aa9a6004294e070adc8bacbe30314000366c006fe907486e1) (by decide+kernel)

private theorem _ECD:WideCovered band66 8824328 9383210:=PRB band66 Z1.f1155 8824328 9383210 (WB 206367807512 16 0xc708124350b6946a3cb4ab1c20481602d63028ea4b8c30811df5ab47cd23871170c20474482ced418d93d2c30811cb94b295ee342d830be0470212c71968c82eec2f8119644b0e5722fe9f30be0456ef2c06ac8b720ac2f81122b0af99f62ba6630be0436bc2bb42f8a6126c2f810a9faae04ee2762d2fbe0422872b65a0895042bef81073eeaccada231f42fbe0412ce2b1cda883f5ebef810315eaba86e1edbb2fbe04061caab49a872e79) (by decide+kernel)

private theorem _ECE:WideCovered band66 9383211 9942091:=PRB band66 Z1.f1156 9383211 9942091 (WB 206367807544 16 0xcf2814b714c92a0b2f6897965028f9898f76b65caf672ca0511acb1a1d6cb51b3e5940a106362862b961af5cb28141a38c3ce8b2b25079630280e9984c9de5428472c604f51fb04d2aca40cf658c09d2e1601e7193f92ccb181370bcbf1cb126e1758e30266d097bc2f24ba1231c604bfdc2f27c2492feb638c097b1b5dcdc091d764c71812f38cba47c5229de58e1025bd3572b0c2431a031c204aaf8ae1665481f076384093b085babcc8fb59c) (by decide+kernel)

private theorem _ECF:WideCovered band66 9942092 10989993:=PRB band66 Z1.f1157 9942092 10989993 (WB 206367808600 16 0xe3181e9448954af453d8d4f1840eda0449408629a83178c2075b5923c76f94b1fc3c610398b6d1a2570a47efde3081c0ffc8b267c51b70cef8c0da57344a95628974d37c606987821b73914298a1be30348d4d0a6190a03b6cdf181a014a83dafe4f95446f8c0ca59441988127866937c6061067a085a793a1181be302e1f8d05169c9bf7dcdf1812177e8725b54d737bed8c0ad0ac3aba16667584f3ca0547e99977fb1318a5f9e5029de88ca93a0983cbd) (by decide+kernel)

private theorem _ECG:WideCovered band66 10989994 11548875:=PRB band66 Z1.f1158 10989994 11548875 (WB 206367841304 8 0xeb2812d6905a1abdb038cbeb281233ce5792baaf27e6eb2811d7ca551fc2ae1702eb281159865335b4ad061ee71810da3d515551abf53ae7181055dc4f6f95aae456e718101b134d768fa9d372e7180fb4074c09fba8c28d) (by decide+kernel)
theorem covered66:WideCovered band66 (AX band66) (tail band66):=(_Q1 band66 7077824 8824327 11548875 _ECC (_Q1 band66 8824328 9383210 11548875 _ECD (_Q1 band66 9383211 9942091 11548875 _ECE (_Q1 band66 9942092 10989993 11548875 _ECF _ECG))))
def band67:Band:=⟨10,55,3681,4547,21999468660106636⟩

private theorem _ECH:WideCovered band67 7208895 8551130:=PRB band67 Z1.f1159 7208895 8551130 (WB 206367909016 23 0xb6d821f4ec826c00d8827adab6d821f351426a92e88235ddb6d821f07f8269fd2881f0e0b6d821eecd8268816881abe3b6d821ed2ec266f1b88166e6b6d821eaf18265b8988121e9b6d821e6a442651ef880dcecb6d821e0ea02645f288097efb2c8307f9ad39c96c78052f2b2c82980e40b83f4e77fc8f8b2c82719e18824edf77f3efeb2c82604f8c6f74cb77eb504b2c82f9d785829ff967e2b0ab2b7614e2681a638a57d1716aeb8217b7341c77be47aef2eaeb8215f5d01be582479db3aaeb821478381e1871478c746aaa820cff1c0fd1c9377b352aaa820bf7100fb4a03769f5eaaa820a04a410e1c73758b6aa697c0973840bb04d2747776a6978082b280b07821736382061820038bc006ea20724f8e) (by decide+kernel)

private theorem _ECI:WideCovered band67 8551131 9116282:=PRB band67 Z1.f1160 8551131 9116282 (WB 1305879435352 16 0x618418eb37564679c58d3d30be0c68952af7dbe2a420185f062aab956b7cf140d0cc2f83100f4ab0f3f897c8c617c185918553865c4794930be0c1d1c2a92e1e21a26185f0604b55549f070fbd3cc2f82fdb7aa9f1c38754a4617c17a798553cc1c3655530be0b9f1daae09ce1902c37df05b3f2157890d0b6d6dbef82ca89cab55cd852cbc5d7417db204f271e4251612eba0bdc96278a3c210632175d05e215d3c7d69071d9cbae82ec5f09db2688304d4) (by decide+kernel)

private theorem _ECJ:WideCovered band67 9116283 9681434:=PRB band67 Z1.f1161 9116283 9681434 (WB 206367807512 16 0xcb18344292bb32ae4ee86b2c60d01e62e8255933020cb1833d02cb91b4e4a989b2c60ce5482e0b22921c2cc71833689eb6f3424648cb1c60cd6c92d7efc910838c718334f4cb5005e41f8fb1c20cd03aacef758ff444c708330d98b308ce3da92b1c20cb416ac87808ee050c7083292f0b1605a39595b1c20c942f2c2c3e8dcc5cc308322bcaafb1a235098b0c20c85042bc0928cb868c30831fb32ae563630b9bb0c20c7bb5ab4fd88ba474) (by decide+kernel)

private theorem _ECK:WideCovered band67 9681435 10387874:=PRB band67 Z1.f1162 9681435 10387874 (WB 206367808600 16 0xe32838706c83af88cf40d171941b6623423383675b6bb8ca0c8e9ca21b4b738b375b6506f6e60e7e6269b45c6cf38361dae655960cd18e9679c1aef583242fd6669f633ce0d751c98f4283323bbd9e506b9560c633d99893e4cf2835918e626dd6cc04f567941aae7d30eecc65dffc33ca0d47e3184b70b2debed965069cc90c13581966bfccb2834aa2860066acaf10165941a4a422facbe25560232ca0d22cf17afdd1299c1d963068e884bc1e08944414) (by decide+kernel)

private theorem _ECL:WideCovered band67 10387875 11518178:=PRB band67 Z1.f1163 10387875 11518178 (WB 206367841304 16 0xef28330b285600c4afc0e2eb2832678e53ab36aeaceeeb283213195165d8ad98faeb283190674f9311ac8506eb28311d144e170cab7112e7183094444c5131aa5d1ee7183052924a8912a9492ae7182ff5a1491df5a83536e7182f95b94816f0a72142e3282f1e8046caf6a60d4ee3282eb20b45803ca4f95ae3282eab894438b0a3e566e3282e599b43a5f9a2d172e3282ded0d42da7fa1bd7ee3282d6ecf422567a0a98adf282cd11141905a9f9596) (by decide+kernel)

private theorem _ECM:WideCovered band67 11518179 11730110:=PRB band67 Z1.f1163 11518179 11730110 (WB 206367841304 3 0xef3834c01d5d6e7fb2fcbeef38343d0a5a7657b1e8caef38339a4e5809e6b0d4d6) (by decide+kernel)
theorem covered67:WideCovered band67 (AX band67) (tail band67):=(_Q1 band67 7208895 8551130 11730110 _ECH (_Q1 band67 8551131 9116282 11730110 _ECI (_Q1 band67 9116283 9681434 11730110 _ECJ (_Q1 band67 9681435 10387874 11730110 _ECK (_Q1 band67 10387875 11518178 11730110 _ECL _ECM)))))
def band68:Band:=⟨10,56,3576,4520,25973242036553917⟩

private theorem _ECN:WideCovered band68 7339966 8518524:=PRB band68 Z1.f1164 7339966 8518524 (WB 206367909016 26 0xb6d84216d7025cd15881fb7cb6d842131e025c182881b5bbb6d8420f01c25b6df8816ffab6d8420a66c25ad8a8812a3ab6d84206a742598cb880e478b6d84201fb82589258809eb8b2c858df729a6a90f68058f6b2c84a2cac8b058b167fcd74b2c8487df508b298067f41f2b2c846903706c911667eb670b2c848924b8bf5a0777e2aeeb2c84369d7ed17df977d13ebaeb8431292838d70d67bfce7aeb842d4b3837cbd467b7165b2c8427b0604979fc57ae5e3aeb841746b01a9b15479cedfaeb8415c4201d4d9d478b7dbaaa820e18f40f697b277a0d8aaa820d09dc0f822927689d4aa98008db6c0dd7ec17572d0a697c0a64980b96780745bcca697608adf80a897637344c9a698207bac40c62e72722dc5a288007df2c0a9767171a243a287c0893e4098fe607116c1a287c08362809922b0708b3f) (by decide+kernel)

private theorem _ECO:WideCovered band68 8518525 9018519:=PRB band68 Z1.f1165 8518525 9018519 (WB 1305879435352 16 0x617c29504153854e44ce4bb0be148cf1a9b384224445585f0a3c3f54d5cb9110b26c2f851879ca6b7ac87fa11617c28882953804043b747b0be142230a9bcd5e1b8c377df0a04ec14b1f650caf16bee8514fa89c2e7185cc095f742891344dc52cc2a043afba143672a6d8c8612d41b75d0a0f3f936d06b085309bae84ff0889bbcf5839e025d6c288c274c03c24189402eb614409b25f3f720b32fd6db0a1d6192f33c9050dfcb6d850d1ee9765e882413d) (by decide+kernel)

private theorem _ECP:WideCovered band68 9018520 9589942:=PRB band68 Z1.f1161 9018520 9589942 (WB 206367807512 16 0xcb18557526b3d9764952db2c6154bcbacb96291c934c7185511c4b1eece44f6cb1c6153f7fac3d0290b230c71854ebb6aff356409abb1c21536de2bbab88f9b2cc70854a33aae2d0a3c3eab1c215169eab50838e8428c708541048ac826637e29b1c214f215aaf4728d6d24c70853a878ab245e33868b0c214e1ae2a9e7b8c5620c30853627ea9d35a2f2a7f0c214cebeaa4c5f8b3f1dc308530f12a895162ace6f0c214b8e4a9f6d98a2819) (by decide+kernel)

private theorem _ECQ:WideCovered band68 9589943 10161363:=PRB band68 Z1.f1166 9589943 10161363 (WB 206367807544 16 0xd338588d36c7bc7b3619a7a670b088e58c5d1e6a05473ce15ff1cb12dc7ccfae7e79c2be59961a60f996a4ecf3857bb48c1db0731bd999e50af4f5980dc46614d2b3ca15db492fd2b8cbe3e467942b95d15effd2973c46cf2856ec3ebcd8052d61899650ad5391775af258950b2ca159b71ae9fb94acce065942b2e705ca598950e3ecb28564e0ab810652905799630ac69e16dccd24fdceb2c6157ec6ad7e2e49b5dc658c2adb2e5a65aa92e037) (by decide+kernel)

private theorem _ECR:WideCovered band68 10161364 11268495:=PRB band68 Z1.f1167 10161364 11268495 (WB 206367841336 16 0xeb2852f6034cfd1555f8c7f39c29362925b6a22ab6a2f9ce14774fd2791e953870fce70a35de490bd90a8ac83e738513b8d46e65153cac0739c286339a2e7f0299f9f38ce1412295131ac54acef1c6709fb3c0879724a45074e3384fd0d6426ae2519cb8719c27b87f20e69428889b38ce13bf1650573214216d1c6709cdfd4824dfe9ff465e3384d943940bcff4f6eb0f19c263333a0c5f027719778ce12d477d03f5f3395eb3a67098ce3c648d269b9855) (by decide+kernel)

private theorem _ECS:WideCovered band68 11268496 11911345:=PRB band68 Z1.f1163 11268496 11911345 (WB 206367841304 9 0xf34858e16c62cadfb5c0b1f34858074e5fd156b4a9aeef3857313c5cf11cb392aaef38565d155a2474b27ba6ef3855da59575ff1b164a2ef3855282a550b57b04d9eeb2854800552ec7eaf369aeb2853d5bb50d74eae1f97eb28538f9c4ee1aead0893) (by decide+kernel)
theorem covered68:WideCovered band68 (AX band68) (tail band68):=(_Q1 band68 7339966 8518524 11911345 _ECN (_Q1 band68 8518525 9018519 11911345 _ECO (_Q1 band68 9018520 9589942 11911345 _ECP (_Q1 band68 9589943 10161363 11911345 _ECQ (_Q1 band68 10161364 11268495 11911345 _ECR _ECS)))))
def band69:Band:=⟨10,57,3517,4493,19588168101133170⟩

private theorem _ECT:WideCovered band69 7471037 8463947:=PRB band69 Z1.f1168 7471037 8463947 (WB 1306953278584 21 0x1b76c30ffc8212bc8c781264b58b21c9d0b949987af406fe2ac590e61931269938d2014aed62c86b26860b8839c8ff8b64b164341a7f44017b3c7f38a858b219c352e1bce2623f55cf2c590cb6f9a8f8726d5f87a5162c86350b3a9d170fafa0900ad5c318c9e81b8c0c47bea6d56ae18b74960da91923daeb1ab570c48158062cff91eb41655ab861bba0839942e8f4869eb164319ba03283e7fc79b64556ae188cfec09c9e85bc949daa55041f3cb81f60b41e270c952a820ecf4c0f8ada0ef043ca95410688fc079010876680a54a60020ca6036f1d93aa6fba952f013db38152ef45d0cf8d4a9820a1ba80bba130e633a0a54c10480da05df890728cc6) (by decide+kernel)

private theorem _ECU:WideCovered band69 8463948 8806951:=PRB band69 Z1.f1169 8463948 8806951 (WB 1305879435320 16 0x5f7c38dc014cf55f8662275f7438baea4cdfe185d51d5f7438925b4cd9658548135d7438f0c94ba7ea84bb095d7438e7fe4b6f928474855d7438d95b4b5546842dff5d7438ca6a4b23e683e77b5d7438baf34b188c83a0f65d7438aec54afbaa835a715d74389f374af4ac8313ed5d74388e0b4af12282cd685d74387e6a4ad98e8286e35d7438696a4add6c82405e5d7438563e4acb2a81f9d95d74383b6b4ada3881b355db743822994ad0f4816ccf) (by decide+kernel)

private theorem _ECV:WideCovered band69 8806952 9384644:=PRB band69 Z1.f1170 8806952 9384644 (WB 1305879435352 16 0x638c3a778f55aeb9c7996231c61d34e12a9b11e3a96e98e10e962515301a71c3162c708746008a8e8338d8ba763843a0755545521c67f4eb1c21cebf02a09f1e31c64d8e10e6f3b54f622f17c912c708733bb8a74a338b577f63843978e6537cbdc5653ab1c21ca57e29b295e28f5b38610e43a3d4da2cf1360c5c30871447aa7e987892358e1843802db54baf1444b2770c21c03bb29937062025117df0e46f4135de310ef874bef871fdbc9a631886ef31) (by decide+kernel)

private theorem _ECW:WideCovered band69 9384645 9962337:=PRB band69 Z1.f1171 9384645 9962337 (WB 206367807512 16 0xcf3877f12abb68da600d873ca1df569ae83d6977657cf287795ccb8f83a5ba5373ca1dd4bbadf7ce965c43cf28770c68b6c34e573ce73ca1db28b2d79ef954230cb28769ea8b4c63652d49f2ca1da274ace78a94281dcb2876770cb26d764e6c4f2c61d96ee2c51fd930e09cb18761a1cb067824a03ff2c61d74f32be1a091f3f5cb18758ec8aedcf6459bb32c61d513d2b834290d9e2c71875282ead2bc24133631c61d42dfab11c78fbfce) (by decide+kernel)

private theorem _ECX:WideCovered band69 9962338 10792771:=PRB band69 Z1.f1172 9962338 10792771 (WB 206367841368 16 0xe748705c3042d868692bd0f9d21bf3981092b05a3952fe3486f2ea441cec3689ec738d21bb20910590a9a16108e3486e11f34172006811bd39ce1ac953912b5599f2ce1df386dcf6239b0f4a784b374d21b332c8c7cb619cf8b9d3486cc1d5318af0671aebf4ce1b2e21cc483dd9bdea6d3386c9c7730d39966d46734ce1b1f0b4c216e59ac492d3386c592b303168668de234ce1b0d2dcbf70ad99aa7ecf386c10132f8bb926475d33ce1b006e4bccfe898906b) (by decide+kernel)

private theorem _ECY:WideCovered band69 10792772 11948157:=PRB band69 Z1.f1173 10792772 11948157 (WB 206367841304 16 0xf348795bf460d790b6507df348789d0c5d5d1ab53669f34877d8315ada36b41c56f33877083058401fb30242ef387631ee559c89b1e82eef3875ba13530acbb0ce1bef38752529514fa0afb407ef3874797f4f4ed7ae99f3eb4873c98e4d53faad7fe0eb48737ba64b591dac65cceb48730b764a1b23ab4bb8eb48727c0848a343aa31a5e74871e4784730b2a91791e7487181ef45bf36a7fd7de74871624144bb54a6e36ae74870e59a43c183a5c957) (by decide+kernel)

private theorem _ECZ:WideCovered band69 11948158 12092580:=PRB band69 Z1.f1173 11948158 12092580 (WB 206367841304 2 0xf7587b69f167aed5b884a4f7487a6e726469e4b76a91) (by decide+kernel)
theorem covered69:WideCovered band69 (AX band69) (tail band69):=(_Q1 band69 7471037 8463947 12092580 _ECT (_Q1 band69 8463948 8806951 12092580 _ECU (_Q1 band69 8806952 9384644 12092580 _ECV (_Q1 band69 9384645 9962337 12092580 _ECW (_Q1 band69 9962338 10792771 12092580 _ECX (_Q1 band69 10792772 11948157 12092580 _ECY _ECZ))))))
def band70:Band:=⟨10,58,3461,4465,28088668841156719⟩

private theorem _EDP:WideCovered band70 7602108 8259066:=PRB band70 Z1.f1174 7602108 8259066 (WB 206367841399 17 0x2cb225cb3ad636d3f7e05fab2c8935b114b77e8df5dda6cb225ea96184cfd1fce8d7aeb88d01c63834ffdef2ecebae22b2dbccabf8f7b3d21aeb889bf1f36942ddeaba42bae2141734db6fb37a1ffeaeb8899bb7bb5493be645b2bae21e4bcc83123df902daaeb8871301214fc97e1d126bae21e30dc993f22f7e5b7aeb886330e232c1f9de79babae2118a7079c99df75725aeb882bbaf202bc17dc3f76aaa190a0984446ed76c893aaa8235aaf0f60c03d8e80a9a5f0afcc82d8884751cdf) (by decide+kernel)

private theorem _EDQ:WideCovered band70 8259067 8642293:=PRB band70 Z1.f1175 8259067 8642293 (WB 1306953278584 16 0xdcba2088f9f095bfc2c1ef7aeedd104329304b0cb160e5eb376e8820eef0258f59b06a0c9bb74410107812d077583091addba207ced9097022ec160e96edd103c0c584bf12d609ea2376e881dded825c7b29046681b97440f7fde129d85381ebf75ab6208a30608bc9d940d2572d5b1044e24045bf90a0575956ad8822454022d4fc5022c38b1644e206d6d85d77980ced358b2244711242a01f8402020ac5911519aa14ffe2e1fec6c162c888320dc7aca030fe463cb16443405dc3138f687e948c) (by decide+kernel)

private theorem _EDR:WideCovered band70 8642294 9025518:=PRB band70 Z1.f1176 8642294 9025518 (WB 1306953177176 16 0x62c2247a0da8f2aea26dfb982f892d4829a58ed89295d60be24a6c1a67b586226b2d82f892477099ff21880c39debe247c35a671a261df69d7af892aa6e972f5086ef165ebe24a461a5c2e621a9f357af89277e096e1348660845ebe24978425aab921864ed7af892429696769485d1f25ebe2489492591322162aa97af8920430961e7c8543615ebe2476b42587f2213f06772f891b3b295fc8c84b4cfddba24620d2577e2211b61f72e891573c95ca6c84263e) (by decide+kernel)

private theorem _EDS:WideCovered band70 9025519 9609482:=PRB band70 Z1.f1177 9025519 9609482 (WB 1305879435320 16 0x65944b360d56bd2192a10a65944b268f5656e3921278658c4b0b7c55db7b9183e6658c4ae1d955766b90f554658c4ab8c355395d9066c3658c4a959254d7b58fd831658c4a7ca754a1ab8f499f658c4a64d25448f38ebb0d638c4a4b6553ed3f8e2c7c638c4a25e253d52d8d9deb638c4a035153860f8d0f59638c49da94533c918c80c7638c498cbb5371638bf235638c493d61536c578b63a4e38c486e5854cd418ad512638c48759553d67a8a4680) (by decide+kernel)

private theorem _EDT:WideCovered band70 9609483 10193445:=PRB band70 Z1.f1178 9609483 10193445 (WB 206367807544 16 0xd348999948bf403b37144ba67132fef17b89a26bee4f4ce2650402f2fa14d3680e99c4c7bf35dbe0e99de70d33898b408ba7625329fbda67130c789725a9a6305333ce260b622df7864c195d679c4c0a4f5b683c97a429cf3897ff7eb572492e2b319e512fc50568ae0a5a1c1b3ca25e7722cd7224afc3a67944ba96e5928de9569e2cf28970bd0b188f129b6a39e512d7fe960f3ba5132ff2ca25a922abd94049df16e5944b42c9574dd2932f9b) (by decide+kernel)

private theorem _EDU:WideCovered band70 10193446 11178884:=PRB band70 Z1.f1179 10193446 11178884 (WB 206367841368 16 0xeb5892f98e47476b2aa4e13ad6249e2d518e410a97660eb5891ef46453e402a164f79d6244f0d90fc4bca73c1ae75890ee80431aa72987bdb9d6242c38909a114a501d3e758905b5641f2c928f92bf9d623f04d90565c8a2c78ce7488ec99d41f0e8286a9a39d22355a75030f72a08d45e3488dd08f39f99b67dc0875d223594e8c68fd49e52fed7488d4034314ad327711b35d22346030c3a8749d35dad3488cf2c63098ad2729d234d22335fecc0d5b89c18b7) (by decide+kernel)

private theorem _EDV:WideCovered band70 11178885 12273815:=PRB band70 Z1.f535 11178885 12273815 (WB 206367841304 15 0xfb689e2f416d5b5cbb4897f7589cea1a693ec8ba2b74f7589bae0d654cb5b90e50f7589aed6f61d524b7f12df75899f66e5ecdc0b6d409f34898e7685b7a7fb5b6e6f348981dfd589feab499c2f3489787525635f2b37c9ff33896c9025406c9b25f7bef5895f0095187e0b14259ef58956ac24f6c27b02535ef5894f7914da757af0812ef58945e004c1488adeaeeeb5893ad464a4917accdcbeb58932f5f48adadabb0a7) (by decide+kernel)
theorem covered70:WideCovered band70 (AX band70) (tail band70):=(_Q1 band70 7602108 8259066 12273815 _EDP (_Q1 band70 8259067 8642293 12273815 _EDQ (_Q1 band70 8642294 9025518 12273815 _EDR (_Q1 band70 9025519 9609482 12273815 _EDS (_Q1 band70 9609483 10193445 12273815 _EDT (_Q1 band70 10193446 11178884 12273815 _EDU _EDV))))))
def band71:Band:=⟨10,59,3406,4437,20466459681907597⟩

private theorem _EDW:WideCovered band71 7733179 8766088:=PRB band71 Z1.f1180 7733179 8766088 (WB 206367841368 16 0xb6c79b966b5ef2d72170a22cb1e5e6b49473a0484a254b2c7950e9849a44220e0886cade4b16150389b08261eeb2b7911b023b9b2520506eacade4033b8e22944802187aeb78eb39834998e1fc0552bade359ed8c482847de121aeb78c964a301bd91f303baba9e3262a8b7567c7ba0baaea78c269f2d812c1ea021eba9c29c18ca1e136796054aeb8a6d0fc2083265e100829a5e20acc072f5f877b007a69787fdaf1c4be91dc7fb69a5e1f7874704d8c768fd3) (by decide+kernel)

private theorem _EDX:WideCovered band71 8766089 9503880:=PRB band71 Z1.f1181 8766089 9503880 (WB 1305879536728 16 0x658c5166ec0151f55d220910cb18a2c1c042a0b08a41d1bd9631456cf4853d91147f22ab2c628abea10a746a28f543b658c515499a14d0bed1d8844cb18a2a07d4298e5ba38d0219631452be105306a346d1f731c628a2f4e0a575228d13d5638c513d93414b4cf5190777c718a262bc8299533a2fce878e31448b550535fb945b1c471c628859f10a87a958ad36e5d6bca8455c8f88f791486a8b6d78da3cb4bb0e412248c856daf13d02e1115b5e4401772db1e20cca21c1153c86e2bb) (by decide+kernel)

private theorem _EDY:WideCovered band71 9503881 10094114:=PRB band71 Z1.f1182 9503881 10094114 (WB 206367807512 16 0xd338b9c2fcb960da68188b4ce2e5cac2e04e1997609d338b9276eb702fe6397bf3ce2e35292d74719855d5cf38b8b8eeb4951e5f16f33ce2e2767acdec79735a2cf38b886acb20a6a5a96233ca2e14c7ac45f396156fcf28b80d38b0455e5615573ca2dee4b2bcc2e94f53bcf28b76848ae5f6651948b3ca2dce142b642693d508cb28b7195aac70564d13bb2ca2dbd88aae7ab92b4d5cb28b6d38caab8ca4892ef2ca2dad9d2a64409194a1) (by decide+kernel)

private theorem _EDZ:WideCovered band71 10094115 10905686:=PRB band71 Z1.f1183 10094115 10905686 (WB 206367841368 16 0xe758b15f45432d09699a15b9d62c40eb5096a55a54822e758b0978e41ef9d6909fbf9d62bebde109b695a307bceb58ad9ed144028e6879e279d62b125f509fa6ea0c756d758adff4831e43667e9c8b5d62b7c6a4c5a80d9f1709d748add22731132c67a1bbf5d22b6aeb8c2e7099df6d5d748ad8367305dd16759af35d22b564c0bffe349cd6a2d348ad324f2faae02711a234d22b492b0bd55a89bb66fd348ad18432eec1726c99574ce2b40ee0ba6f0c9a963b) (by decide+kernel)

private theorem _EEA:WideCovered band71 10905687 12086154:=PRB band71 Z1.f535 10905687 12086154 (WB 206367841304 16 0xf758bc2a5c6256a4b86b8af758bb37c05f1f17b74b56f758ba2ba95bfba3b62b23f368b921d958ede8b50af0f368b8a04f565cd6b3eabdf368b7cea35402e0b2ca8af368b6fc4351b730b1aa56ef68b626174f7475b08a23ef68b5de254d9b24af69f0ef68b53b6e4bdf0bae49bcef68b48dea4a3292ad2989eb68b3f21648ec88ac0956eb68b38b6f474efeaae923eb68b33a1b45e4c7a9c8f0eb68b2a41e44c509a8a8bceb58b21abb441c39a78889) (by decide+kernel)

private theorem _EEB:WideCovered band71 12086155 12455050:=PRB band71 Z1.f535 12086155 12455050 (WB 206367874072 5 0x1f6d162de1c791701be0c8afb68b082ba399d76de762bfdb457fbe81baff1aef3093eda2bd0a6ad4a2937557e1eeb15d26c466147bb98bbd) (by decide+kernel)
theorem covered71:WideCovered band71 (AX band71) (tail band71):=(_Q1 band71 7733179 8766088 12455050 _EDW (_Q1 band71 8766089 9503880 12455050 _EDX (_Q1 band71 9503881 10094114 12455050 _EDY (_Q1 band71 10094115 10905686 12455050 _EDZ (_Q1 band71 10905687 12086154 12455050 _EEA _EEB)))))
def band72:Band:=⟨10,60,3352,4409,27382108303674737⟩

private theorem _EEC:WideCovered band72 7864250 8460753:=PRB band72 Z1.f1184 7864250 8460753 (WB 1306953278584 16 0xdbb63087c2d0891b16408ce8eddb1842b4d844a18b203440562c8dc294d99166d77011062b16467308a868949ca7ff68f58b23268a5e2126e253fb276ac5918f17320d1c5f09fb4d3162c8c6bae845eb8994fc8354b16454c8b907d58cb07db00958ae31072910f76b353e4662ab5718714dc86f51589efec915ab8c300d0032c6c44f6d304ad5c616acc01bb09ea7ad7e156ae307a0100e7899d3d231fac5918f4c3a52861989e6d2755ab8c2452ac23f94f2f245f8ad5c50ec4e20fcfa1078915a) (by decide+kernel)

private theorem _EED:WideCovered band72 8460754 8759006:=PRB band72 Z1.f1185 8460754 8759006 (WB 1306953177176 16 0xdebe3462d7a5389ae169b7b7ef8d0f16c95d203855e0edfbe34145c25aa94e1454f77ef8d07928954c8a84cc6cdcbe3475d5a4557b6120e6d72e8d2966e8a2864843acb5cba349fd4227c0c20fc7e572e8d265e889c4fc83a9295cba34927822696120d816172e8d22e488971b88317875cba348307a259b220b3adb6ae8d1ebe28938688285e6dbb63470a3224e72208f4536ed8d19ba489135081f444dbb63459e1a249cc206adcf6ed8d13618890f008162a3) (by decide+kernel)

private theorem _EEE:WideCovered band72 8759007 9131821:=PRB band72 Z1.f1186 8759007 9131821 (WB 1305879435320 16 0x63846a144c4c283b8b572d618469ee7f4c02b38ac58c618469bf5b4bef8d8a33ea61846981ac4bf59d89a249618469f5a44aca128910a8618469e7564aaa9488c7d7618469d6894a9a2e887f06df7c69c6ad4a78be883636df7c69b2404a71e687ed65df7c699f9a4a535a87a494df7c6986814a5476875bc3df7c696f994a3b128712f3df7c694f2e4a48ba86ca21df7c6931574a386c868151df7c690e334a3a96863880df7c68e7fe4a5fc685efaf) (by decide+kernel)

private theorem _EEF:WideCovered band72 9131822 9728326:=PRB band72 Z1.f1187 9131822 9728326 (WB 1305879435352 16 0x67946beef85596e54a38a333ca35e13baa9d8ea4f7e919e51ae5f9d538765269c06cf28d700b0a916d692bc6267946b66fc543859491560b2ca35a59da9f4c7a46647d9651acb12d4e7f75220efacb28d623a0a633d69075dc65946aeb4f52d6c747f21d32ca355e56a94f6ca3d4a619651aa1b2149ed751d81eecb28d4a60ea500468e2f55659469e9f652f24346ceda72ca343900aac2a5a34304b8e31a6e03945d97b18f4e0c708d460be98fd708be8cf) (by decide+kernel)

private theorem _EEG:WideCovered band72 9728327 10324830:=PRB band72 Z1.f1188 9728327 10324830 (WB 206367807512 16 0xd748db81c8bd4b1a762d7b5d236cccd2f03ef9cf9bcd748dae14cbad2ce71a06f4d236a2ddae64f49bd67ad348da598eb8491e6d13634d2368f07adaf989ab337d348da1fecb56c666886574ce367a8dad1210998ff3d338d99e8cb349d263f94b4ce3653a0ac92db986cb0d338d8f92ab14c965f6c3f3ce363040ac133d97496ecf38d89e76af4b0a5adf333ce361f0c2b918c96262bcf38d85f96ace08a5652273ca360bdf2afa609502e8) (by decide+kernel)

private theorem _EEH:WideCovered band72 10324831 11294151:=PRB band72 Z1.f1189 10324831 11294151 (WB 206367841368 16 0xef78d461c547841e6b1571fbda34ef0c51982e5ab3283eb68d30a4a4553b26a83d03ada34b277d1188b1a8ebfdeb68d292014307bb69f22ebada347e6710a8745a6a576eb68d141c4428d6b69608cfada34129ad0c3a95a45ef1eb68cd78df43fe91e8ceebb8d633d3424e7e382a2186bdb58ce7b53319440683d49f6d63393fd8c4d1d9a06386d758ce230f30d3ea67f47935d63381ee4c1c9759f4043d758cdf81c30039327aba875d23379b30be85c49e1cff) (by decide+kernel)

private theorem _EEI:WideCovered band72 11294152 12487159:=PRB band72 Z1.f539 11294152 12487159 (WB 206367874072 16 0xff78d1a4f7bad1be5f44fbfdb4685fdedc0ca3ef59ad3eda33fbea8d6ad057886e3f6d19edb0c672f21bb202efb68ced0e531ccdf5cfe75fbb4671c15980a7a6e366a3dde336b48cb8bf396f6ccbeef19a8ed8599be9b69323f778ccd1a9ab89d65ab7eff9bc662e00d527b2ed13273cde3302272a41d9f6652b3e6f19766894fdc6db20616f378cb55cca7071ad8716977bc657ae8531365abefe3fbde32ad272952d755d3899def194fd4148bb54ad790a) (by decide+kernel)

private theorem _EEJ:WideCovered band72 12487160 12636285:=PRB band72 Z1.f539 12487160 12636285 (WB 206367875096 2 0xff78d368aaa0655230341f7fde34a10e07af2a8bfad3a) (by decide+kernel)
theorem covered72:WideCovered band72 (AX band72) (tail band72):=(_Q1 band72 7864250 8460753 12636285 _EEC (_Q1 band72 8460754 8759006 12636285 _EED (_Q1 band72 8759007 9131821 12636285 _EEE (_Q1 band72 9131822 9728326 12636285 _EEF (_Q1 band72 9728327 10324830 12636285 _EEG (_Q1 band72 10324831 11294151 12636285 _EEH (_Q1 band72 11294152 12487159 12636285 _EEI _EEJ)))))))
def band73:Band:=⟨10,61,3301,4380,25792752774519185⟩

private theorem _EEK:WideCovered band73 7995321 8494494:=PRB band73 Z1.f1190 7995321 8494494 (WB 1306953278552 16 0xdbb6388db390854357819d9edbb6388cf79085394f8178d3dbb6388c2ff085312781540adbb6388b5b80852b03812f3fdbb6388acc7085274f810a7558b2351c18c45a441a80e5aa58b235964024d829d080528058b232c326d2629a3c7fbf5758b2326996d2030ca87f2c2d58b22dbc2555fff5dd7e990458b2315645012a23647d72b158b2312695e10710847cdf8756ae30ff62c0ec5bb07c4c5e56ae30dca7e0d7efe87bb93456ae30b9f0f0c909e87b260b56ae308de010c154707a92e1) (by decide+kernel)

private theorem _EEL:WideCovered band73 8494495 8692279:=PRB band73 Z1.f1191 8494495 8692279 (WB 1306953177112 16 0x5cba3c9fcca240a384a2375cba3c947e223b8a8458a25cba3c895da23cfb840f0e5cba3c81bfa2370d83c5795cba3c78d8223389837be45cba3c9eb6217e7483324f5cba3c9b1621795f830d85dbb63c9755a1746d82e8bbdbb63c9371a16fa382c3f1dbb63c8f68216afe829f26dbb63c8b3421668c827a5ddbb63c86d3a16249825592dbb63c8240a15e418230c8dbb63c7d78215a74820bfddbb63c7873a156ec81e733dbb63c732d2153b481c269) (by decide+kernel)

private theorem _EEM:WideCovered band73 8692280 8993667:=PRB band73 Z1.f1192 8692280 8993667 (WB 1306953177176 16 0x60c23ceb9a2517bbe24ee0d8308f390f09435db88f1ed60c23cdb892505b9e22a1658308f332bc9434c7885ec460c23cb341a52cabe2054c18308f2654a951c5387cb9a60c23c6c7a25870ae1e081b8708f00c1c98ff8f873872dfbe3c993fa4be53a1bbb777ef8f2426691dee586a548dfbe3c797424864b6196ed37ef8f1743892786586121fdcba3cc1cca26fe7217222b72e8f2e8e8898d44857ef55cba3cb219a25731214d58572e8f2a554892e5c84ebcc) (by decide+kernel)

private theorem _EEN:WideCovered band73 8993668 9426911:=PRB band73 Z1.f1193 8993668 9426911 (WB 1305879435352 16 0x67947a86a052fb1047ebeff2ca3d14cf299b8d23d12d79651e6bea94df9e71d6319cb28f324b8a40ff28e1e62638c7a83a04c1206c6c59cb1c63d3009a5e313633e03d8e31e907912e5afb18c9ccc708f4e76e967e208bd1bd63847a65254b1d0645c414b0c23d2ae0257dc322cfa4d8611e915992b6b1915e9fec308f467e49575948aab6a61847a212e4a9be44530eb30c23d0672a53f0822861018611e7db05298719139d58c308f3c844948e98898517) (by decide+kernel)

private theorem _EEO:WideCovered band73 9426912 10029686:=PRB band73 Z1.f541 9426912 10029686 (WB 206367807512 16 0xd348f9e014afe31a6429db4ce3e6a272bb76298774dd338f95a0aae247a5f908f4ce3e3f7aab4f819750fad338f8a352ac580a5af7434ce3e1deaaadc8f962aa7cf38f84ab8aa8ba6565df73ce3e0714aa68d8950454cf38f7e974a8d9be51c4af3ce3deb912a101293de01cf38f77696a757624d2b633ca3dc4eea9ad8c92b7aecf28f6b238a63c524892173ca3d9a02a974e591915bcf28f611d0a5827243f8cb3ca3d691a295f0f906b08) (by decide+kernel)

private theorem _EEP:WideCovered band73 10029687 10632461:=PRB band73 Z1.f1194 10029687 10632461 (WB 206367807544 16 0xdb68fdba48c50563447a1bb6d1fb31d587103e86a78f6d63f54ea308079d08b5d6dac7e7c7d603e46a08390db58fca716bf42953fe0cfb6b1f893f97ba7ba7d74f75d63effceaf18294f650a6bac7dee755d73c09e36ebd758fbbc7cb966353b4783ae91f712917009b27442635d23ece5dadba504e3eb76ba47d75755af7d29bea45d748fa903eb4c3a536ae37a691f48f7d6729026b0fcb4d23e88feac981d4d186469a47d00a458931e999da0) (by decide+kernel)

private theorem _EEQ:WideCovered band73 10632462 11762664:=PRB band73 Z1.f1195 10632462 11762664 (WB 206367841336 16 0xf388f821d950778c59bdf479c47bb6fba719a22c95657ce23dc2df5324111625e85e711ec9a1095cb00b008efef78f5859a49466a57714e77bc7a68c7240f602b6f127bde3d270091a5b75592beddef1e850b08ab4eaab6fa4ef78f375af44677f5524a8f7bc79655aa20b0e2a48bfbbde3c739710e44054ff957def1e2025c86ead8a6d659ef78ef0e7e457db852d80377bc76c586222da869226cf6da3bc6d30c8829d46c6c1b6d1dddeae636376a2d036) (by decide+kernel)

private theorem _EER:WideCovered band73 11762665 12817520:=PRB band73 Z1.f543 11762665 12817520 (WB 240727613464 14 0x20711eb5a2f45e6b261ca3840e23d2468283eb27c26e1d81bc79c4040fb99fb828f94ff78f2738a1ddba8b0085ddfef1e3475d38bc9edf7d923fde3c39f7e6d427cbdd4d27db4780f760d1800d795cfefb88ef5bee191bc5aee20b1f711ddc55f304715dd30ecbee23b970ec5db312b93b877bc476e3718b50cd3702a68f788ed431b95db7aedbbb85ef11d9f8c92a8eb8dae4473de23b21da852c383b4a23b) (by decide+kernel)
theorem covered73:WideCovered band73 (AX band73) (tail band73):=(_Q1 band73 7995321 8494494 12817520 _EEK (_Q1 band73 8494495 8692279 12817520 _EEL (_Q1 band73 8692280 8993667 12817520 _EEM (_Q1 band73 8993668 9426911 12817520 _EEN (_Q1 band73 9426912 10029686 12817520 _EEO (_Q1 band73 10029687 10632461 12817520 _EEP (_Q1 band73 10632462 11762664 12817520 _EEQ _EER)))))))
def band74:Band:=⟨10,62,3250,4351,30030782034601352⟩

private theorem _EES:WideCovered band74 8126392 8516562:=PRB band74 Z1.f1196 8126392 8516562 (WB 206367908984 16 0xbae904abd40e9022fb03e7a57df2030a8c9ea74536073a96eba46b1c3e60bb34240d4bcdd748d4a0f4c2321ac81844dbae919f818d8044df902be4175d233b7c33081357204e7d2eba45ad2a156820a5c08a6459646b067de8f2d36280ef9bb2c8d7c5ec13b7b3c3014a856591a0c6391bbe6062004246cb2329e32021942583fbdefd9646419500351ce087ee72eb2c8c6b9304583ccd0fca4f965918b55df89737d21f6f72ecb231373491092f183e948cd95c621b8341d9f1a07c9468) (by decide+kernel)

private theorem _EET:WideCovered band74 8516563 8678340:=PRB band74 Z1.f1197 8516563 8678340 (WB 206367908952 16 0xbef91506e09357503211af12eba409488d0852dcb84216bbae9025084c2147bce0ff0feeba4093b2208511fb83d713bae9024e294213987e0ec79aeba4093129084da9f838cb9bae9024a43c21345ae0d9e3aeba4092037084cb13834261bae902459d821320de0c74d6eba4090ba8084c94f82f808bae90241528212bbce0b4b72fbe44555b9592a9d282adb0bef90d9607d30e8aa60a220efbe4326fe64fdef75826356bef90b460bd56611e608f8aeeba419ca6d389ed5c8218fe) (by decide+kernel)

private theorem _EEU:WideCovered band74 8678341 8982863:=PRB band74 Z1.f1198 8678341 8982863 (WB 1306953278584 16 0xe1c24093847094f71e4488a7f0e12048da684a207ee231bd78709023a4202526c4710f93bc384811ebbe12697328832445ebe409d639089912cc3f3f62f5f204e4620449c3c61e764d7af902704f8223fbc30ea674bd7c8136fcc111a1a98708e15ebe409ada1088a630c35f44af5f204d3c38442754619d0c17af90265948220f8430c53aebd7c8130722110669185df7e5ebe409714f08806acc2ca936e5f204ad7184403e46152b357af9163edf93a716110a00eabd7c8ace9cc9b9193884b61c) (by decide+kernel)

private theorem _EEV:WideCovered band74 8982864 9306418:=PRB band74 Z1.f1199 8982864 9306418 (WB 1306953177144 16 0x64c6453fdd25cff6c70099316322aeca52c2fea35b2018b191556aa95ad291a4450c58c8a9c764ab7028cd7cf62c64549a7254c664646bb316322a1ead29bd3a310c758b1914eb4494c4bd17f18ac58c8a62194a58868bae6c62c645279ba51da045b20a3163228e0c928ddea2c66e98b19143d48947149159ec5c18c8a042c4a301c8a8509e1c244f30ba517f5451d58f0e122705d52914ea27c15f8709132cf094cda1134bffc384896b7d4a6f0c895ba7) (by decide+kernel)

private theorem _EEW:WideCovered band74 9306419 9915463:=PRB band74 Z1.f1200 9306419 9915463 (WB 1305879435352 16 0x69a48ca236552de54ba623b4ce463c972a5ad7a5ade55a672311c8151f0952c45c8d339183474a83cb6958e32699c8bfb0653c3794a7cc0b4ce45ea1129d122a519341a6722eb2614d559d27a03cd33916ec58a6abda933b6de79c8b3cdc53272b49535e73ce457a5d29879ca48482f9e7229da3d4e75d522fab3cf3913afcaa865f290e8a8e79c894659548242c829fb32c64576be260cf323efd1596322b3c1d2f6a311e5526cb191550c8979c808e95e2) (by decide+kernel)

private theorem _EEX:WideCovered band74 9915464 10524508:=PRB band74 Z1.f545 9915464 10524508 (WB 206367807512 16 0xdb591d4d3ebc35ae825d736d6473f47aec688a002abdb591c9feeb9c0f27db7e76d6471240ae2a529ed948d7591be8a4b74a9a79125b5d646f06dad797c9dafe5d7591b9b52b4c856746ccf5d646ddc6acd5339c8682d7491b43a6b24bba6fc7475d246ba26ac4d6f9b5d20d7491a8790b01e4e6b21bf5d2468aa0abd3d89a33bdd74919fe5eae359a667c334d24673f72b5b2a990a5ad34919a39aac4cc261d6a74d2465ded2ac8e197e0f7) (by decide+kernel)

private theorem _EEY:WideCovered band74 10524509 11476141:=PRB band74 Z1.f1201 10524509 11476141 (WB 1305879469144 16 0x79c48afc41241bb3b5e395af389154613472c266b7cd2de7122902e68c8ac0d664f4bbe244f08b5140575aba08677bc89a422223ccdb54ee46ef79128b0b446eda6a53705def221dee08b39e0d4122f7be2434be1520e0dba6fafb75b48833ac1d49c354ba330df690fa5f031c79b692a0d5bed21eed8262c584d209c237da43d2724c42321a37ed26fb4878b6b98502b345d442db690ee3d3303ceb28955bdb6d21d9fa05fc87e50e05f36da43af2fcbddebca12c0d) (by decide+kernel)

private theorem _EEZ:WideCovered band74 11476142 12694232:=PRB band74 Z1.f547 11476142 12694232 (WB 240727612440 16 0x81c489bce5de446a306cb6206f22509b073af11c089767fc488cdb89ba7372fd804dff3221cbe069cbcabe36b07fcc881619195b6d2f43535f7321efeed61ce71bbe3eb7dcc876b2c9795692eaea21f7321cec505b1597b991267dcc86f976d61deeae19f0def321abe79558549b73e617bcc866fa294c3ea2d853f9ef3219554950c6a5b4eb9b7bcc86220a13bd852cf08e1ef1217b6964d393ab298d679c485b23112c750ac5bdcde712168ba749751eb04610) (by decide+kernel)

private theorem _EFA:WideCovered band74 12694233 12998755:=PRB band74 Z1.f547 12694233 12998755 (WB 240727613464 4 0x83cc8c54b393069a78cb0c7079917277aa3ddb1f14bc0607122b881b43bba66202cf40e2451b2587fc5f7c2dc3b) (by decide+kernel)
theorem covered74:WideCovered band74 (AX band74) (tail band74):=(_Q1 band74 8126392 8516562 12998755 _EES (_Q1 band74 8516563 8678340 12998755 _EET (_Q1 band74 8678341 8982863 12998755 _EEU (_Q1 band74 8982864 9306418 12998755 _EEV (_Q1 band74 9306419 9915463 12998755 _EEW (_Q1 band74 9915464 10524508 12998755 _EEX (_Q1 band74 10524509 11476141 12998755 _EEY (_Q1 band74 11476142 12694232 12998755 _EEZ _EFA))))))))
def band75:Band:=⟨10,63,3192,4321,30273512462773490⟩

private theorem _EFB:WideCovered band75 8257463 8555506:=PRB band75 Z1.f1202 8257463 8555506 (WB 206367908984 16 0xbef92dee6152b8a5ed0517e57df25a049ca76f663a09998efbe4aef6615523f2b41206b5d7492fbafe71be655821b47bae92397630ecb953b03eb7575d276f2bdaf2f41320740aeeba4ed47325ed14e240d54e5d749d9becebf1dffc81850ebae93ae7c017eb761902bf0175d27531a72ff9e9f204e7caeba4ddab2755d53d1c08a31d9646e410c4b40ad7280eed4b2c8d8b38e93dc93c300b13765919c89751783c2c1ff098acb2328dc7d1f969743f9614596463b682c2e78dc07e95ef) (by decide+kernel)

private theorem _EFC:WideCovered band75 8555507 8709335:=PRB band75 Z1.f1203 8555507 8709335 (WB 1306953278584 16 0xddba4899ef6083d04242726beedd244c9e6041e39d212fd2772e9226201c20eff39093374b974912faea107429c84742c5cba48974ed0839cce42274f2e5d244b5f6041cd77210a43d72e9225997420dfae9080702b974912b88210701ac83ddf25cba4895128083871641dc32ae5d244a52b041b77120e4b597af936bc3ad6672bd706da8ebd7c9b5301ab7d66bb8347b95ebe4d878785cf0019419115af5f2692f92ad1e56e60bf2757af933caa556d76b6305ae1cbd7c98d0c42adde51882b180) (by decide+kernel)

private theorem _EFD:WideCovered band75 8709336 8968921:=PRB band75 Z1.f1204 8709336 8968921 (WB 1306953177144 16 0xe1c24cbf6024350ac46d6cf0e1264e055235636223ef17af9343af287fa01108940bd7c9a0c6443dbaa87f9835ebe4cfb8021e95943d733af5f267a0690ecc4a1d8d297af933be5487270d0e305abd7c99ccbf4393da86cd115ebe4ce0ca21bbf54340faaf5f266d6310d741218db617af933314486e4290bd779bb7499cd99421b6a85a09eddba4ce246210a3e42bd88eedd266f0f5080fba15560b76e93364f083fb810a5fe9bb7499a83e41f82e850a65) (by decide+kernel)

private theorem _EFE:WideCovered band75 8968922 9276579:=PRB band75 Z1.f1205 8968922 9276579 (WB 2407538546776 16 0x3131935f170942e7a8d8ca33131935c460940e8e8d418631319359a3c93bfc68cf66a31319358008936cc28cab4d313193562dc9345d28c60313131935464493175e8c1514313193531b292ca728bc9f7313193513fe9296a68b7edb3131934d97692af5e8b33bf3131934b5f2927cb28ae8a23131934848a9263d28a9d867031933de4e935b9a8a526870709332b0c9442728a074cb0b0930e920983b4189bc2f7070933682491e9dc8971137070932fe38922b3c8925f6) (by decide+kernel)

private theorem _EFF:WideCovered band75 9276580 9872666:=PRB band75 Z1.f1206 9276580 9872666 (WB 1305879435352 16 0x69a49cc5bf537c904b528d34ce4e48f2a99e0d2583b85a672717b454b6dd92af150d339387222a55c8c94e26f699c9c0d83528efc4a261b34ce4df042a921e024ed7f1a6726e8c3d492251263f87cf3936a6a6a4e79c92898ae79c9af8f452769448f9a873ce4d2d16a99e1d245745f9e7267439d4ccc27218dbdcf39331a14a554269030a5658c9b25ff4b0726c7cd3632c64d8019a5798b63c10c996326b61312af8e31cdbf2c7193615889483d48dd7c0) (by decide+kernel)

private theorem _EFG:WideCovered band75 9872667 10487982:=PRB band75 Z1.f545 9872667 10487982 (WB 206367807512 16 0xdb593dc4ecb848b28022bb6d64f5883adb9d09f7275db593d0576b5c6267b70f36d64f28fb2d29619e4603d7593c6f22b3395a76bf2b5d64f1117ac84d79d1990d7593c19feb0eab6720d5f5d64efc7eabd93f9bed1ed7493b9b8cae88aa6d5b935d24ecfdeab6c2f9ac0abd7493ad07aac91a668a9cb5d24ea6752aef99999439d3493a663eaaeffe63f8034d24e8d172a724b9867c6d34939fc7ca8fd4e5f46374d24e70bfaa062b973b54) (by decide+kernel)

private theorem _EFH:WideCovered band75 10487983 11334042:=PRB band75 Z1.f1207 10487983 11334042 (WB 1305879469144 16 0x79c49aa5b7a2e96cb59e334f38934530f44f0b56af14a1e712670d088983a0d54c5abce24ca44c913d8b1a96c4279c4985928a31b9d3507fa1ef892f59fc445cdda9c4d79bef2608100640202d2f375b7de4c0a37cc5fbb1a550b26fbc9809b39886f834974f0df692fe45030a81129090fdbed25f6af4609cd851c70337da4be148cbfd330a2f7cd6db497a69d17c4ab144c328db692f2f2a2f2e632872d69b6d25e33ea5d9262509a90b6da4bc169cb986d8a09ee8) (by decide+kernel)

private theorem _EFI:WideCovered band75 11334043 12564674:=PRB band75 Z1.f547 11334043 12564674 (WB 206367874072 16 0xffa9327213b774d2dfdc617fd498c00fda7ac7efa3143fea4c3cf86cb8f177abfbbff52606a7f61e921bc336afba92f7aea2f1977dd837c7dd4977a2c96c7156e76a1beea4ba0522b0234d715c27f7325be30a555b9ab781a0f7992d734aa9952f5b2a977bcc9689cfd425be6d4a2f3de64b2e8c89cdffb67f893ef32588d5f4c88f3b2cfd6f3992bdfbba58f2e58d1b279cc95c5fa5255852c1dbcbce24ad88848f4a8b5e94ffe71256212946dd59ae1e0c) (by decide+kernel)

private theorem _EFJ:WideCovered band75 12564675 13179990:=PRB band75 Z1.f547 12564675 13179990 (WB 240727613464 8 0x85d49f517656a44ad9238ad07993c2805a9c95631fbf920f3273e4e64d5f34e361b8c1e64e20f7c916621c596fe83c49b79f3911777988d51903993582352031f370cf86a07526908be3d1538e108d3c0ea4cdd558745a21c0e534) (by decide+kernel)
theorem covered75:WideCovered band75 (AX band75) (tail band75):=(_Q1 band75 8257463 8555506 13179990 _EFB (_Q1 band75 8555507 8709335 13179990 _EFC (_Q1 band75 8709336 8968921 13179990 _EFD (_Q1 band75 8968922 9276579 13179990 _EFE (_Q1 band75 9276580 9872666 13179990 _EFF (_Q1 band75 9872667 10487982 13179990 _EFG (_Q1 band75 10487983 11334042 13179990 _EFH (_Q1 band75 11334043 12564674 13179990 _EFI _EFJ))))))))
def band76:Band:=⟨10,64,3109,4290,30290426686969845⟩

private theorem _EFK:WideCovered band76 8388534 8582779:=PRB band76 Z1.f1208 8388534 8582779 (WB 206367908984 16 0xbef955210715f075af05ecf77df2a6373829f117da0b422efbe53e2479492fe7ac1554ddf7ca76c5b499c5f7d8284aabef94d5cab53c2257b04bd7575d28f60ee1bc015b208e32aeba5165eb23993ab241096d5f7ca13027e7a5f05c81ece9bae95a007354efccb5038df175d2b8cc502e40c14e068426eba56524155359a4140bd8c5d74ac98142a85668a815528bae958a51a54e81025025e6f75d2b137d5aa7b95ea042522cb2357732f3f9ff74c071abd9646f82bf2b8dc7c8809776) (by decide+kernel)

private theorem _EFL:WideCovered band76 8582780 8757600:=PRB band76 Z1.f1209 8582780 8757600 (WB 206367909016 16 0xbef94276c142094a5885a160c3095259fc156a6717857b70bef9590474d382999485557fc3094f0f3659e55dd685099fc3094ad35d190ae86584e3aebef957b3661323884484bdbec3094ba055f527bad38471debef94df3a94b9e0ad2844beebef94dc6bd0ba1e3a28425febef958b8f4950fb4c184000ebef9589241554be2b183da1dbef957efaf15285f4183b42dbef957d295d589a271838e3cbef957c412d60e9d7183684dbef957c74996c28cb183425cbef956e5b856bd2eb0831c6c) (by decide+kernel)

private theorem _EFM:WideCovered band76 8757601 9068394:=PRB band76 Z1.f1210 8757601 9068394 (WB 1306953278552 16 0x60c250ac1aa08681c38a5f6a60c250ab8b5086436b8a138960c250aaf6708605a789c7a860c250aa3dd085cfcb897bc760c250a9191085b3db892fe760c250a7dde0859c4388e407dec250a688208589f7889827dfbe50a51310857db7884c46dfbe50a377b085791b88006660c2516183c3a16fba87b48460c256d20de595e9c18768a460c256b2ab15a077a1871cc360c2569ccfe5bc452986d0e360c254f649b47b2c8c86850260c254bb94d48439b486392260c254603b6483de3885ed40) (by decide+kernel)

private theorem _EFN:WideCovered band76 9068395 9379187:=PRB band76 Z1.f1211 9068395 9379187 (WB 1306953177208 16 0x64ca55cbbd24a270b1e3ae6c994ab833649332763b4649932956dad892482ec742d932652ad577124602d8e39d164ca559e18a487c5b1bdbe1c594ab1ff6490b6763688438f1956013292196ec6ab1871e32ab756524530d8d0a4fe3c6555a972492b7b197cdfc78caa86ad49413b631ca3b8f1954a72c92a51e46135771e32a8981d24eac38bdacce3c6550598a486335171dd9c78caa181f4856c462d0c2f8f1953963c917e74c57b95b0612ab20810da7388aab4a) (by decide+kernel)

private theorem _EFO:WideCovered band76 9379188 9942499:=PRB band76 Z1.f1212 9379188 9942499 (WB 1305879435352 16 0x6ba4ad34ef52c7bc4bdaf1b5d256845e2946b425c788fa692b3687548cd192d0cc4d349594370a3f81895eea069a4ac59d651ef904aab6ff4d255fdcca90595252fc7ba692ae0b3149c389284ebbd3495593e8a6f618938f9be9a4aa47a55379e7497bed33ca55ff3aa565a064980699e52af5fbd2a84f32390b0cf295756fc9503d5913097e594ab7ace4a4ceac84c6b32ca55de48a4d3c424004559652aecee125ff991f6a68cb295754ee92b1988f6953) (by decide+kernel)

private theorem _EFP:WideCovered band76 9942500 10564086:=PRB band76 Z1.f551 9942500 10564086 (WB 206367807512 16 0xdb695efbc6b584ae84c7db6da57b27ead0caaa09a36db695e98d8b2dc3e8009d76da579a282c5fdc9f6ab3db595e193eb05ace7b4bcb6d6576d23abd61b9e3b31db595d496aae5812768dbf6d6573e572b564b9d0baed7595cc35cac1a3a71cfb75d65723132ac17e9bdc2cd7595c539eaa01b26d11af5d65706532a3ecd9aacaad7495bd7a2a7fb826853a75d256d9a629d3e5997d27d7495affe4a6ad8263959b5d256ae1f2985cc984da5) (by decide+kernel)

private theorem _EFQ:WideCovered band76 10564087 11341069:=PRB band76 Z1.f1213 10564087 11341069 (WB 1305879469144 16 0x79ccaad81ca2aebd35a1a1af3995502f54478f86af7629e732a667948b665ed557047ce653c9bf11fd8a6a97e8671c4a8ca1299074db509e08e3795170a731981a69edd09c6f2a2764862653cd38fc0b8de54410e8c33455a687c071bca863cb182df114bdffedf795094372ff53629560f9bef2a0f5005f1b4452603eb7de54185fcbc92fca428bc6fb4a82274975f3d14721f4df6950134a2e6be028be4e9bed29fb5765c15e25130bcb7da53e8f24b6d41ca1c9b7) (by decide+kernel)

private theorem _EFR:WideCovered band76 11341070 12584243:=PRB band76 Z1.f554 11341070 12584243 (WB 240727612440 16 0x81dca97d171a990270014cdff72a4331666246abed5b07fdca892f5d86246af698b5ff72a158635decc7bc76ac7fd4a8025796ba18aed1ca5f7529ebe8b5804caba17a77dd4a7670e954e982e3a091f7529cd41a5251eeb7b8a27dd4a6f4be5410dc2da2481ef529accd24e4b62b5599d7bd4a67e265319a2ad0a86def3299a1194a9238b2fa997bcca62b59d238946c72c59ef3297cec147b52cb09b9479cca5b5eed1ab8debdb045e732964e7f45dc44ae3c90) (by decide+kernel)

private theorem _EFS:WideCovered band76 12584244 13361225:=PRB band76 Z1.f1214 12584244 13361225 (WB 240727647288 10 0x91d4ab1212c9c7d7bf2f81261752a190a8173badccab0c785d4a7abe70548b96b26051217529c7be693b3218c851c383cca6a004049a70031c89020f7298b125913fa58c5f2bf83dca5dbb34410f883130cf20f7295ff110f58b84c393b981dca5318aa3a51c4b0990de077293e43b0ddc7dcc134b5) (by decide+kernel)
theorem covered76:WideCovered band76 (AX band76) (tail band76):=(_Q1 band76 8388534 8582779 13361225 _EFK (_Q1 band76 8582780 8757600 13361225 _EFL (_Q1 band76 8757601 9068394 13361225 _EFM (_Q1 band76 9068395 9379187 13361225 _EFN (_Q1 band76 9379188 9942499 13361225 _EFO (_Q1 band76 9942500 10564086 13361225 _EFP (_Q1 band76 10564087 11341069 13361225 _EFQ (_Q1 band76 11341070 12584243 13361225 _EFR _EFS))))))))
def band77:Band:=⟨10,65,3064,4259,30222602817208330⟩

private theorem _EFT:WideCovered band77 8519605 8676568:=PRB band77 Z1.f1215 8519605 8676568 (WB 206367908984 16 0xc309728cb2b73f8e3f08c9b17df2dc519d1726cb1a10fa1efbe5be0d3d3368686c20c1a5f7cbc92238a88697483f1e2bef9788e8614f5c22907971f7df2f10aadaac0fe520e94fafbe5dfd67c559ece641bf75df7cbc00580b08652c835898bef977209455fdb93706648d7df2ed194bacabf0ae0c2fd2fbe5cec14751fdc794172d15f7cb9c8152ad94f4a82bf4fbef96f3984525324630531fb7df2dcfb9fa7092fc609caaefbe5b370f0519fae4c1262cdd74b36990e70986e8822606) (by decide+kernel)

private theorem _EFU:WideCovered band77 8676569 8931636:=PRB band77 Z1.f1216 8676569 8931636 (WB 206367908984 16 0xc7196f6a65d334106b1092698e32da701b2bf27df61ff23f0c25ddf1fb49a4171c3d7f5e184bde8498b2558f4876345c3097ba723d6c1fb490e2d438612f514fcad2b87b21b27f30c25d05d554759e41c33eac6184b964f048d7c3b38630b4c3096a58b60a48be350bc8218612d3f7a714d1b40a16f6f70c25cccc8d537d410c2cbb5e184b92b886aba8891857119c30971a25b16bf73730a958f8612e179c9b18654e61491d2fbe5e250534c473cc427f115f7cbbe702496bdd6884b17d) (by decide+kernel)

private theorem _EFV:WideCovered band77 8931637 9245565:=PRB band77 Z1.f1217 8931637 9245565 (WB 2407538648184 16 0xb1b19627879824b040b1a26fa62632c592aa043696f2331b5cc4c658b1474086b396463d199898cb16070810cec7c8c2d8e7031962bc19021975e917c1d4e0e12c56ddd843250522e5115c1c258ac72508613ca45a3d0b8384b155dbc10c15948afafd7070962a5ae02176f69155cb2e0e12c53ca2042f10922986d0c8ca5c92f0de16bee1c50a879898cbd17076af56e6a89c86a3131979b7765655b35512f78c62632f2d44eae517e2a24bc84c4c65e05b6d5dc2788c4713e9898cba291c6adf9d888895d8) (by decide+kernel)

private theorem _EFW:WideCovered band77 9245566 9559493:=PRB band77 Z1.f1218 9245566 9559493 (WB 1306953177176 16 0x66ce5e05cd24ef90a4777159b3977ed3c939b6691912066ce5deff224e09ea4511f393397792a89340b290f7d7e5ca5dd761a4cd13a42accf97297728e492fb86905e8ee5ca5dba31a4c042a4047ab972976a43c92fa1e8fc546e5ca5d961a24bdd3a3de287972975faa89330028f2bfce5ca5d6d5024cca5a3b7d639729754d5493ab168e92b3e5ca5d3b34a4fc47a39183f9729744f2e94c68d8df96ae5ca5d14db24e03d236b31b9729738ee69485b08d6021) (by decide+kernel)

private theorem _EFX:WideCovered band77 9559494 10167729:=PRB band77 Z1.f1219 9559494 10167729 (WB 1305879435352 16 0x6dacbdf99e54095a4d92d8b6d65ee9aca9d2cc26a319daeb2f6a6b94d16d933e63cd7597af706a5d5d49959d66bacbd47395296ca4c6046b5d65e851ea926312609d11aeb2f31e814954992f1bf4d75978fac8a4e7f496f4b16bacbc172952bc364b2db475d65da05ba9f2c7257087fa6b2ecfa1d4aaf6f2a51add34976ddeca1ec12948f8d679cbc31854ab2f6c9fb2233ce5dfe7ea556ee64d73ed9e72ef0fe92a03ab258764cf39783cda940584922a69) (by decide+kernel)

private theorem _EFY:WideCovered band77 10167730 10795586:=PRB band77 Z1.f557 10167730 10795586 (WB 206367840280 16 0xdf79705b2c5d1d29497485bef2e07f88b8b35a9083e77de5c093796e4d051c3d86fbcb80594ad799da2ee68df696fe5a95a3d6b44aa3dbed2df5fb8b3474286ef577da5bddc916426e5091466fb4b7a355ac37b3a08943db696f2ab657d3ed3fdff3b6d2de1ceaaeb1327d5ac36da5bbc72d5b1064f5eb3edb4b76a892b11bc9e241fdb596eaeab5591673b15adb6b2dce928aa405e73c6336d65b8fdf152c444e2c21edacb70f382a220d9bbefa) (by decide+kernel)

private theorem _EFZ:WideCovered band77 10795587 11737371:=PRB band77 Z1.f1220 10795587 11737371 (WB 1305879469144 16 0x7bd4bc768024e8873663236f7a978734d48405c6c79a25ef52f015b28dadb2d859fc3de65dd2ee919ac91af81657bccbb1c0522f571b5c9da6f79974d35045e7bd6b47103ef52d922029ced30d5f4d7bbe25cda884ecf2c2aab71c73c4b8ea6398eb0c3530914e38971948931608b6a3ad05c712e2dffa61fa2cd428fc38e25c54800c1e4aca7b8af71c4b89bc798096594e3ecce37971068f2faf2c29a1875c6f2e19cbe5e9eda52f66a38de5c2504cbbbd44a5538b) (by decide+kernel)

private theorem _EGA:WideCovered band77 11737372 12993085:=PRB band77 Z1.f559 11737372 12993085 (WB 240727613464 16 0x83e4bc2e5ad0960018c847b07c976c27c1f2f22b143eae0f92eba8493b605061ee8d41f25d2952270fcccc2aa8781e4b9c26b8d7246382efeb03c972c70a19a91fb01158a0772e3fa73317c2d5f8968bfee5c4a17a5f24bcbde03e7fdcb82b3a4b6ed6d795b58ffb97000179622caeedec69ff72debbb52ae6d75d24443eee5baebe8532902b915f67ddcb718910a22b0f6fc6c8fba96df7b193a6c9edac349f752daee262661045abf203eea5b416ce4b7620b44bae) (by decide+kernel)

private theorem _EGB:WideCovered band77 12993086 13542460:=PRB band77 Z1.f1221 12993086 13542460 (WB 240727647320 7 0x12ad96bdeb3537889eb3a90f24f72ec06b6ab5bebae6b8d543ee5c702a22fb1f2ccc3f1887d4b82a4b6581f1b196190d0bb96ef5374a237b732767d21792dbcc5d92bc9886453b142f25b42eac2355fbcc774d0) (by decide+kernel)
theorem covered77:WideCovered band77 (AX band77) (tail band77):=(_Q1 band77 8519605 8676568 13542460 _EFT (_Q1 band77 8676569 8931636 13542460 _EFU (_Q1 band77 8931637 9245565 13542460 _EFV (_Q1 band77 9245566 9559493 13542460 _EFW (_Q1 band77 9559494 10167729 13542460 _EFX (_Q1 band77 10167730 10795586 13542460 _EFY (_Q1 band77 10795587 11737371 13542460 _EFZ (_Q1 band77 11737372 12993085 13542460 _EGA _EGB))))))))
def band78:Band:=⟨10,66,3020,4227,30350649023428112⟩

private theorem _EGC:WideCovered band78 8650676 8848840:=PRB band78 Z1.f1222 8650676 8848840 (WB 206367908984 16 0xc3099b4c8b562687130e0b9186132a65f823a390e21ae1830c2650b0ab471ccec43357be184c9883a48f6d830861d8fc3098a42138a3f5f5d0ba04d86132765b7a8dee7f616a5cb0c264d127255758c6c2c15f6184c9035a6ae74c75855c09c309914e665796ca9b0a6aab86131f4890b2cc0332143a870c262c77296050d11c273f6e184c2ee194bac169284c138c30980fe53b26397a3093509861315c733e89304c611cf42fbe639773c2dc0c9c42268e5f7cc71e8445c05180842667) (by decide+kernel)

private theorem _EGD:WideCovered band78 8848841 9165904:=PRB band78 Z1.f1223 8848841 9165904 (WB 206367909016 16 0xcb298af4be0a32194c8bdc50cb2995fbdb95d11a1b8b8ee8cb29950e01577007bb8b417fcb2992598598c2851a8af417cb298b6d17d70e94898aa6aecb29811c88937e6f888a5946c7198e78104ba1aee78a0bddc7199b5ac156871b9689be75c7199a7aa316ac026689710cc719991e1a56a2e7f58923a4c71995ed875534ce1488d63bc71991c370931074a38888d3c7198f990013e18693883b6ac30987f9e34e498d9287ee02c3099785a2521df6c187a099c3099c32bb963cc4a0875331) (by decide+kernel)

private theorem _EGE:WideCovered band78 9165905 9482968:=PRB band78 Z1.f1224 9165905 9482968 (WB 2407538614392 16 0x73739856f74894cd0ac8596c39b9cc2a3e844ac79564195c1cdce614321c25bb38b20300f6565309ded912d92ac8fca9f727298573ca090a30dc7be9b59394c27a6a84a0338e3cbf39c5c6616c52821ce5651dc4cae26330b4fec10dfe128e94fd71319859e12086c6354723ca3898cc2c94bc435cb2a37e8b1c4c66161c7e21a1c451b5986626330af7bc10caf528d5f5b313198574678862bd54688f99898cc2b60dc430384a33122cccca602e275f3cf6e318ee42646532d5fd04fc84588c29b9) (by decide+kernel)

private theorem _EGF:WideCovered band78 9482969 9879298:=PRB band78 Z1.f1225 9482969 9879298 (WB 1306953177176 16 0xead665ca6ba8f0d0a5afc09a34999100c95a76996243168d26633d22558236562581a3499897b694c16594ee8ee6d266360125340d2514efb9f3998a93c94baf4940656e6ce661e9fa51eff24ee3b79b3998487a94407c936b85e6ce6604a8a5023a24c78719b3997d83893d64c92d0b466ce65e3e8a4fad324a0d2d9b3997593a93cbbc9235e366ce65c9ee24edcb247a1ed9b3996ee7e93b178919b1366ce65aaaea4f00024536ab9b39963180945f7c910042) (by decide+kernel)

private theorem _EGG:WideCovered band78 9879299 10513425:=PRB band78 Z1.f1226 9879299 10513425 (WB 1305879435320 16 0x6fb4cf3dac56d4f5a06c116fb4cf03a75671959fd1406fb4cee13955e8739f366f6fb4cebf245574c59e9b9e6db4ce9b2e5505d79e00ce6db4ce7620547df19d65fc6db4ce4b9d542f419ccb2b6db4ce210753a87f9c305a6db4cdece3535ea19b958a6daccdc09652fc999afab96daccd908452b83f9a5fe86daccd554e52ba9199c5176daccd13f55297c5992a456dacccbaa752dc2b988f74ebaccc513053067597f4a3ebaccbdb5352d63a9759d2) (by decide+kernel)

private theorem _EGH:WideCovered band78 10513426 11147552:=PRB band78 Z1.f1227 10513426 11147552 (WB 206367840312 16 0xe789920875622fd5aa1920e78991cd02615fa2a97e4fe78991941a60a69ea8e37ee7899152735fc920a848ade3899125c05ee988a7addde3899109075e2ec8a7130ce38990eb925d4978a6783be37990cb415c93c8a5dd69e3799091585be06ca54299e3799054ce5b2c54a4a7c8e379901bd85a9c84a40cf7df798ffad759e6a6a37226df798fdda85957c2a2d755df798fbffd589d8ca23c84df798fa2a857e302a1a1b2df698f7a17576074a106e1) (by decide+kernel)

private theorem _EGI:WideCovered band78 11147553 12296908:=PRB band78 Z1.f1228 11147553 12296908 (WB 1305879469112 16 0x7fe4cf9772ab28f1aee8b31ff733d343ea71edcba6d2b7fdccec42fa8bf5bae4de25ff7338dd949f21ccb801e87ddccda49826e0482db3115f773355bc2971830b596a37ddccd0cfd24ff7c2d18405f753325ba691fd06b32b5f7dd4cc1394241efdac7d6f5f7532ddafc8fbc4cb0c01b7dd4cad73ca401c0abe29e5f75327ecd89155f8ae54d7fbd4c9235f2380cdeb47cd5cf3324e870652392abe99373ccc9298f190528aad3b09cf332469aa632b70aab3f1) (by decide+kernel)

private theorem _EGJ:WideCovered band78 12296909 13565163:=PRB band78 Z1.f1229 12296909 13565163 (WB 240727647288 16 0x95e4c74ba829c9100f3bf3ae1f7325b74a18dc3c0cdc74a87e4c88a8305a88e8b32469e1fb31fa2f214d6a92cb5c0687ecc7528c84d8c77b28999217b31b0f5212032e4c8f0c285ecc65ab70433d71b1eec7e17b317ede00fe9524c6857e83ecc5a2a903c550c3153f720fb3153b5a0e4fe26c41a3a83e4c51bae6369d91b0b92620f931357ac8d046bac1aef781e4c49999431f312301e556079311c6050bfb390bf43b281e4c4464ea2e52d12f8384207931064c60b35f92bcd86f) (by decide+kernel)

private theorem _EGK:WideCovered band78 13565164 13723695:=PRB band78 Z1.f1230 13565164 13723695 (WB 240727613496 2 0x97c4c99e4bdfd6815d1682f95eccfde45df1f6aad0328d) (by decide+kernel)
theorem covered78:WideCovered band78 (AX band78) (tail band78):=(_Q1 band78 8650676 8848840 13723695 _EGC (_Q1 band78 8848841 9165904 13723695 _EGD (_Q1 band78 9165905 9482968 13723695 _EGE (_Q1 band78 9482969 9879298 13723695 _EGF (_Q1 band78 9879299 10513425 13723695 _EGG (_Q1 band78 10513426 11147552 13723695 _EGH (_Q1 band78 11147553 12296908 13723695 _EGI (_Q1 band78 12296909 13565163 13723695 _EGJ _EGK))))))))
def band79:Band:=⟨10,67,2977,4195,30387986212224041⟩

private theorem _EGL:WideCovered band79 8781747 9101945:=PRB band79 Z1.f1231 8781747 9101945 (WB 206367908984 16 0xcb29b011dd56d51a5f15c4f39653541e2a303e3d9a2a51372ca68a4a5cd6814eec52310e38cdde1cdeaf2c93c89f7f5c719bb0975560b1dc71353918e3373060fab68982a256e731c66e2ad5c58e4b954486b7e38cd981f60946d4d188bf43c719b1820b53506fe310e22d8e335ecd73aa055c86208bab0c26e11c6a484f31843ea5ee184dbb3a908e51ab0878691c309b68fbf119670d10e70c986136b7b9ca2fb56c21ba8e30c26d3b7ab4622c14434e05e184da0ce968e360c0864ddf) (by decide+kernel)

private theorem _EGM:WideCovered band79 9101946 9422144:=PRB band79 Z1.f1232 9101946 9422144 (WB 2407538648184 16 0x72729a2ab8202433e7b1f8a816565344e13804a00df63ddc4dc4ca68b8754085d9d6479473b8b8cd16e86210b592c8edabb71719a2d7ea42161ad91d191ce2e3345a4cc842b26d238f989c5c668b31c008547ae46f81ab8b8cd162f7e10a611c8da20971319a2bfb38213bc391aa7b8e263345754184271a123416c0ccce6c4c812d16ad0dc65bc219194d5fc2824fa99428c695832329ab74d0c9fab9151836566465355ba1b9422048a2f33fcc8ca6d878c25810738c5bf6919194da77974bdc40688b30a6) (by decide+kernel)

private theorem _EGN:WideCovered band79 9422145 9742343:=PRB band79 Z1.f1233 9422145 9742343 (WB 2406464804952 16 0x34693725e15271d5529500e68d26e4134a4cd31a51676dcf9cdc6aac4984bf4a05d7b9f39b8a24092e3c693bd8373e7370d5b92589a526deace7ce6e0b9224ab82a4c84a9cf9cdbf66a494a8949697eb9b39b7a970925e4a9284d1736736ec0a124ce5d246d48e6ce6dc75da4a0dca47a1e1cf9cdb66d0495d0148cd25b9f39b66b729315ae914c1f73e736c06fd26cfcd21fbe4e7ce6d5e42250033a42bf19cf9cda5fd54a7402c830ccd9739b4cc409374d890136d) (by decide+kernel)

private theorem _EGO:WideCovered band79 9742344 10382741:=PRB band79 Z1.f1234 9742344 10382741 (WB 2405391063128 16 0x37da6f68442a36c9e79b654df69bd51a2a826079dd13d36da6f4019a9c3e8e74d390db69bca2a6a66e8b9c988b36da6f0e13a978bce6ff0c8db69bbcd82a4d59f9b5fd936da6eda91a91e0ee6b0e00db69bafca0a458f39a272736d66ea88628eca4e662b38db69b9d162a460ab98ee7536da6de4fea9fc24e614872d769b49f32aba19697b5c375d66de3292891e665c65a8d349b958e294f4c0967d1234d26e3f12250be525782e4d349b8ac5e93fa74954460) (by decide+kernel)

private theorem _EGP:WideCovered band79 10382742 11023139:=PRB band79 Z1.f562 10382742 11023139 (WB 206367840280 16 0xe789b175c05e8759506647c713628ff8bb718e9e5b2f8e26c4a5d573e0ad37d3971c4d88519ae0786a65e19e389b0e9ae5b4b874b8381c6f3616642b56a2294959f8de6c1cd7167eefd2448771bcd81b842cb337a3ecb5e379b016fd58d24346a0b9bef35feea6b028f28ad00f7de6bf60155dfaad10bd56fbcd7dc1e2b744aa17b51df69af908d562e4d41bdf1bed35eae24ab863e810a837da6bc6445557094fd323efb4d77abfaa67149f09ee) (by decide+kernel)

private theorem _EGQ:WideCovered band79 11023140 12063786:=PRB band79 Z1.f1235 11023140 12063786 (WB 1305879469144 16 0x7fdcde83ed27b4d53702854fbb9bbc9524d6a1a6db6de1f77375c760970296dad1633eee6e995b92955d9b46a147ddcdcd9b7247372b6662c6fbb9b896074800466c7e2c5f7736ef9ae90538cd860003eea6d6f1c121973daf874efddcd594f7a9087af5c9d38f399b496773c2677ab457a9cf3365385463db24d5ee9c39e66c9e5fcc5a790ab40df73ccd92ca41878f9955490ce789b23292307a0c2a820b9cf1363e77e601b7254b5eab9e26c6dfb4beb910a8cf7c) (by decide+kernel)

private theorem _EGR:WideCovered band79 12063787 13344582:=PRB band79 Z1.f564 12063787 13344582 (WB 240727646232 16 0x87f4d8377eea92417cb9f4687f4d7915689c8a83ca669485f4d6fcb86915862c92de285f4d6838be88482bc7f53085f4d629a78801311c6bc7f85ecd5c8a2678f467c583cd83ecd576cee731cf3c44b1c83ecd53937c6d1ccfc3126a83ecd4f5428684d41c1d9b881ecd4bb344645e56c0a10681e4d48134a600739bf685481e4d45ba165c4900be2fa281e4d42dd88595b7dbcf6f17fe4d3ffe8e568b91bbbe3f7fe4d3de2765393b1ba858e7fe4d3c1a62510daab94cdc) (by decide+kernel)

private theorem _EGS:WideCovered band79 13344583 13904930:=PRB band79 Z1.f1236 13344583 13904930 (WB 240761201784 7 0x4b79354c48c1620e61750b08a63a9a9861b71b80ad9a5e6e12dfcd5dba727f8174bd1babe96fe6832c46c363911684106ca8135e632fa3f91fc73d256e23e9b3c95b0cbc4d419c21550df4d8e5e585c19450ccd7f8) (by decide+kernel)
theorem covered79:WideCovered band79 (AX band79) (tail band79):=(_Q1 band79 8781747 9101945 13904930 _EGL (_Q1 band79 9101946 9422144 13904930 _EGM (_Q1 band79 9422145 9742343 13904930 _EGN (_Q1 band79 9742344 10382741 13904930 _EGO (_Q1 band79 10382742 11023139 13904930 _EGP (_Q1 band79 11023140 12063786 13904930 _EGQ (_Q1 band79 12063787 13344582 13904930 _EGR _EGS)))))))
def band80:Band:=⟨10,68,2935,4162,30364477474322217⟩

private theorem _EHE:WideCovered band80 8912818 9236151:=PRB band80 Z1.f1237 8912818 9236151 (WB 206367909016 16 0xcf39c41ffdb11facca8ceeb7cb29c7b803cd04f8698c9fc7cb29cbe8ce49ddea288c50d7cb29cb6f5509f956588c01e7cb29d76726159887e78bb2f6cb29d5ea93165418e78b6406cb29d2fb0596a3c4e68b1515cb29cd7896d5a6c4658ac625cb29c51631d3abc2048a7734c719dc30d5957657038a2844c719dad07d5505a39289d953c719da264255481252898a63c719d99b3a95e2a6b2893b72c719d6efced4f5321188ec82c719d24d9c526d65d0889d91c719d0dfc213dd0ce0884ea1) (by decide+kernel)

private theorem _EHF:WideCovered band80 9236152 9559485:=PRB band80 Z1.f1238 9236152 9559485 (WB 1306953245816 16 0xe7ce71658ca120535591ddbde4ca7179ea810d1904918ecd64ca717765410c85f4913fdd64ca7174bce10bf38c90f0ed64ca7171b0210bb97c90a1fc64ca717021c10b2d9490530c64ca716ddcc10b086c90041b64ca716c2a410a86148fb52b64ca716965210a800c8f663a66ce771ebb85f38f438f174a66ce7639c1857b720a8ec85a66ce75e5e9e594523a8e796a66ca74839a84bb92098e2a7966ca768ea647f566d88ddb8966ce7537f70891cf908d8c9866ce728c498a1d00e88d3da8) (by decide+kernel)

private theorem _EHG:WideCovered band80 9559486 9882820:=PRB band80 Z1.f1239 9559486 9882820 (WB 2407538546776 16 0x74349d9b8ee946aa696ccc434349d987f694166a967dd434349d94f5693f9f6962ee434349d9171c93abda95dff434349d8d3b8939f1e95910334349d8af68935b0a95421334349d876ac9365be94f32234349d84ac493327e94a43234349d8199093088e94554134349d7c17a93521e94065134349d7787893553293b76034349d6ebfe9407da936870b3349d665749482be93197fb3b39d545d6965b3692ca8fb3b39d46cb49729cd927b9eb3b39d4059a96a1e8922cae) (by decide+kernel)

private theorem _EHH:WideCovered band80 9882821 10529489:=PRB band80 Z1.f1240 9882821 10529489 (WB 1305879435352 16 0x6fbcef4ae0551165d05568b7de77909d2a4afee8033c5bef3bbd26550724f3ede20df79dd8834a74acf9ed12f6fb4ee8a98535ea3cf19a737da772cc5299235e7655b5bed3b888214be09739ef18df69dbc2faa5bd779c59abedb4ed955252d175cddde576da769eb4295975e6c77abb6d3b301a94c301f350013db69d83936a6e53699e228edb4ec2a8951a764cca223b5d2768bc4253d8e262999dae93b3b4e52938e130110cd749d97a7e94587c976aa5) (by decide+kernel)

private theorem _EHI:WideCovered band80 10529490 11176157:=PRB band80 Z1.f479 10529490 11176157 (WB 206367840280 16 0xe799d2183c5fc7e35511bbcf33a3ed68bdcefaa7abf79e6747539177aa454a68e73c4e8cde42e9000a8af3be789d15e2a5c6e715022b5cf13a23ba0b77a9a9dcdeb9e2743b7796c310d36accf1c4e8667d2d2d54a637b8e389d0ac0e59a7cb4b33afc713a11640b1e61693efdf8de74198e5610c8d22f0b71bce814fe2bdee7a3c035e379cfe9b9573aa34644a9c6f39f7780ad54a68a11d38de73e5e755838d50f349efbce7b916aac768a148b2) (by decide+kernel)

private theorem _EHJ:WideCovered band80 11176158 12226993:=PRB band80 Z1.f1241 11176158 12226993 (WB 1305879469144 16 0x7fe4ef349528fcf6b752362ffc9dd5c0b4fdc886e557bdff93b9b8049bbb46dc0d173ff276fb7c931d315b6de6c7fdced6b03a5afcbb6b4556ffb9d970b34a20ca6d19ba5ff73b0bed492fb86d995943fee75c4be9278289b1ef667fdcea2965a62564b616749fbb9d132d74ba16eabddf8dd753a6ce62655660d71e113aea74d0470c84c18ad9e4175cce9829598cfcf15a00c0eb99d2c36c3130d72b18a01d733a4ff9e61845455e24fb9e6748e930c14d5cab26be) (by decide+kernel)

private theorem _EHK:WideCovered band80 12226994 13520331:=PRB band80 Z1.f481 12226994 13520331 (WB 240727646232 16 0x89fce96c742be246fce4dcb89fce897e12ae4644cd120987fce7dd98aa07568cbd64887fce755dd294aa74ca9a8687f4e6d5d428b51c9c95ec585f4e657666821d8bc8230385f4e5fa5327a7a81c6e74285f4e5adf6c74688ec5ab8085f4e55fa026ef75cc46fbe83ece514b1069de18c333fc83ece4e0ad46497c5c1f83b83ece4a88ce60e675c0bc7981ece471ade5d68f9bf80b881ece44199e5a14edbe44f681ece4270f057182abd093581e4e3fdb4a54bd00bbcd73) (by decide+kernel)

private theorem _EHL:WideCovered band80 13520332 14086165:=PRB band80 Z1.f1242 13520332 14086165 (WB 240761201784 7 0x4c7d3991535954748f35bc0566bc9c3656cefc07659ab68a92e0ce589e807708a63d4789298fa70b314ee569d5d699e68cb8339bdfd92194138748043e5429d265f610366b01a18a9d2a0ce2de78cbb96240cf898c) (by decide+kernel)
theorem covered80:WideCovered band80 (AX band80) (tail band80):=(_Q1 band80 8912818 9236151 14086165 _EHE (_Q1 band80 9236152 9559485 14086165 _EHF (_Q1 band80 9559486 9882820 14086165 _EHG (_Q1 band80 9882821 10529489 14086165 _EHH (_Q1 band80 10529490 11176157 14086165 _EHI (_Q1 band80 11176158 12226993 14086165 _EHJ (_Q1 band80 12226994 13520331 14086165 _EHK _EHL)))))))
def band81:Band:=⟨10,69,2895,4073,30346771875780710⟩

private theorem _EHM:WideCovered band81 9043889 9370358:=PRB band81 Z1.f1243 9043889 9370358 (WB 206367909016 16 0xcf39f3ecfad16388d88efaf6cf39f2c431d15db8178eab42cf39f01eb8d02ff3468e5b8ecf39ef1485512094f68e0bdacb29f17c8fd7b7ab958dbc25cb29ec24b2591398a48d6c71cb29e2d0e4daf9d5f48d1cbccb29e42399196153838ccd08cb29f6f47d930c0c828c7d53c719f857d394e35d318c2d9fc719f65f5b945385318bddeac719f43a5cd3ea0db18b8e36c719f1b92693b445518b3e81c719ef8ef693cfef918aeecdc719ef025a939bf2008a9f18c719e82574155898608a4f64) (by decide+kernel)

private theorem _EHN:WideCovered band81 9370359 9696827:=PRB band81 Z1.f1244 9370359 9696827 (WB 1306953278616 16 0xe9d278aa465093245624fd8efa749e2adf982456f5793a687e9d278a69660921f61e4d5b4fa749e28201024c75d693071f66ce78b6fa6085bf4564adda99b39e2d74d02168d759267b666ce78b4a2c08578ad24860059b39e2cd710215426491c84de4ce78b1ff70852c49245e261a349f07eba509a2bd39128e468d27be5e0546c3390e4364c1a349ed6a0cd29083f290897c68d27a1afa54621124640e71d9b39f54a4b50b3f0708fea1366ce7d192bb41cc26823e697d9b39f41bf090ca34a08f4aab) (by decide+kernel)

private theorem _EHO:WideCovered band81 9696828 10023297:=PRB band81 Z1.f1245 9696828 10023297 (WB 1306953177208 16 0x6ad67e4b34253f29931e302d5acfc89dd4a50492628735ab59f8fd3a9445324c290cb56b3f1cc1127d55c9802656ad67e2f0b24f32472f6560d5acfc465d49d0cae5d8bf1ab59f859ee937c31cb89a3b56b3f04a6126942296c393e8d67dfa89a4cc7352ce7bdd3a4fbd4c6499176a5890aba749f762209320294aea3af4e93ee1d1d269eb19584c1e9d27dace624db9432a6a1bd3a4fb258349d2826539567a749f4f84c95abacca4ad274e93eafe652750f89445f0) (by decide+kernel)

private theorem _EHP:WideCovered band81 10023298 10676236:=PRB band81 Z1.f1246 10023298 10676236 (WB 1305879435416 16 0x71c4ff1dfc55c7a7345d018e379fdaeb8aa8abe2892291c6f3fa903553ca0bd0d49db8de7f3d45aa44d07a109d271bcfe4caa5447fad40d4d4e379fc3592a7de15a7f2c05bef3f794794e1882cf95cc37de7ed0c529b45f59e8c2f6fbcfd539353430293bd98cdf79f9e3f0a66e31275357bbef3f1eb914eccb9ce56faf7de7ded1e2a36c339c0e8cefbcfad07e55dbac536de47db79f6710ea657e866b3ef3aeb3f292bd2ad0984d1829f5d67e39f0253a7e09990ea) (by decide+kernel)

private theorem _EHQ:WideCovered band81 10676237 11329174:=PRB band81 Z1.f1247 10676237 11329174 (WB 206367840408 16 0xeba9f1ff2c610d77159bd2dd733e39272c052d62b0fcbbae67c634f57dbb43d5cfe375ccf8a3feaf477e6ab005deb99f10bc75de3c0d54c1e9cf33e1d504ba025d6a706339e67c3277d70abead49111f3ccf8554e2db7214a882bae789f080095aa6f694fc6a3cf13e08d64b43348e9d0fa79e27c0167165d6f9d3524073c4f7e8aa2c615d2a60518e389efaf85581e1e54acb5fc713df1afcaf2bcc693191f8e27bda9515bc2c0d2136f71c4f7a304ab35470a38775) (by decide+kernel)

private theorem _EHR:WideCovered band81 11329175 12390201:=PRB band81 Z1.f1248 11329175 12390201 (WB 1340239207576 16 0x40f67fb3e8555fdcf2f43ce503d9fe4bc652fe5bbbbd06740f67f41d6d42b7e6aea465903c9fbddc94f1a179b952c43ff27ea6fed37058a2e04fccffc9f9d9da4c3ab87b6d5223ff27e48c3d2cc9edad65944ffc9f8022d4b3a975b4577f3ff27d5ce493540652cc62b6ffc9ee59fa52e3573b1d9db3bea7cd2e14ce0d24ac26c2cefa9f305643301952affba23bea7cb09e0ca32546bd70e4efa9f278f1320aff1aebcd13aea7c909d4c605882b875a0eba9f221993113510ad7dff) (by decide+kernel)

private theorem _EHS:WideCovered band81 12390202 13696079:=PRB band81 Z1.f1249 12390202 13696079 (WB 240761200792 16 0x8b027d4c3a36dfdaa7e87e27c4813e5fde7b18ffb3b3ef5f62409f120ea167bc9bb9cfd5911fcf7e1da2a46e35ccd3fdb86fe7ba36084c59e05e60085437f3daebb9238eb46b2b08e21bf9eca58f90933d739306cf0dfcf5eeba47d3f978c8449684fe7ac9a9d3b5388be382e2427d3d53b2f9c21111b171bca13e9ea11750d5fe0ab89104309f4f4c8a6a669d594c3494f82fa7a45253313e4f1e1053fc17d3d1926e1785420b032eb60bd9e86b604b641c037f19b901ecf4047585821b90be4e0a) (by decide+kernel)

private theorem _EHT:WideCovered band81 13696080 14267400:=PRB band81 Z1.f1250 13696080 14267400 (WB 240761201784 7 0x4d7f3dde18f9a44d07b66d0226bf9eda5048dfe290bb0ea6f3214fa6779e94fd9ecd736659906791ede2ee2103deafbca4b853e22b9fabcd788b52e30a5c39f7c0c915dd6653a6f3e52e1cf9f2b36b81c918d23b20) (by decide+kernel)
theorem covered81:WideCovered band81 (AX band81) (tail band81):=(_Q1 band81 9043889 9370358 14267400 _EHM (_Q1 band81 9370359 9696827 14267400 _EHN (_Q1 band81 9696828 10023297 14267400 _EHO (_Q1 band81 10023298 10676236 14267400 _EHP (_Q1 band81 10676237 11329174 14267400 _EHQ (_Q1 band81 11329175 12390201 14267400 _EHR (_Q1 band81 12390202 13696079 14267400 _EHS _EHT)))))))
def band82:Band:=⟨10,70,2855,3731,30220327299396453⟩

private theorem _EHU:WideCovered band82 9174960 9504564:=PRB band82 Z1.f1251 9174960 9504564 (WB 206367909016 16 0xd34a101c30d66d4a89910734d34a0e46fd9703e5a990b6bcd34a0bdc5f58da67f8906644d34a05fa4218174ab79015cccf2a15474dd6561d868fc553cb2a141c8595c433f68f74dbcb2a137b4cd5e9db758f2462cb2a11d76e951b19458ed3ebcb2a10cbf015476d148e8372cb2a162579d574e0538e32facb2a15019314a792928de281cb1a1394eed39778228d9209cb1a12c61c132d04628d4190c71a11c883d2a000318cf118c71a1108ad526710618ca09fc71a100ccf120988408c5027) (by decide+kernel)

private theorem _EHV:WideCovered band82 9504565 9834168:=PRB band82 Z1.f1252 9504565 9834168 (WB 1306953278616 16 0xebd68075c640967282e583ae3af5a01cb118259507a95be40ebd680701450960b8e655b721ab5a01d931c24bf7d8951d5168d28088e120866b6de533361a34a021fc182190327947c60e6ce8086fc40860aa9a50af9f9b3a0217db82175cf593db6fe6ce8084cd7085b52d64e2bd9a34a091eb712429db4933a7e68d28161c714b61bfce4ba819a34a0195d6b6208c6392998e68d282b985ed8d13a4a492455a33a12fe99d56e59f191f89e68ce849f0e057a2064646a095a33a10b397952707209157ad) (by decide+kernel)

private theorem _EHW:WideCovered band82 9834169 10163774:=PRB band82 Z1.f1253 9834169 10163774 (WB 1306953177240 16 0x6cda84c19da577fc89b163e6cda84ba2fa5666d79ac5c66cda84b2b9a54f0379a754e6cda84aa6da53f5c69a24d66cda84a127a533f4699d45d6cda8497ab2525da59983e56cda848cb4a51e63599336cead6848170a5136b498e2f4ead684741b25107d498927bead684662f250a2d3984204ead6845681a506d1297f18bead68442fa250fa7297a113ead6842dca251623197509aead684175e2515641970022ebd683f370a547b2096afa9ebd683d964a55ddc0965f31) (by decide+kernel)

private theorem _EHX:WideCovered band82 10163775 10822983:=PRB band82 Z1.f1254 10163775 10822983 (WB 1305879435416 16 0x73c50b608756d68ff4a4a8ee78a166bccacc5a3a921161c7142c72655700ded1f1b3b8e2857fa02aa967ca3427671c50adf3d54eb89745430ae38a157720a9184ea880251c7142a4ab150dd1cd0afd238e2853745a9cbda8a0beb371bd0a2ff25365aaf403b84e37a13eb60a6afc1a7df349c6f426dbb94d9e52cf6df0b8e2849ccea9fdf549e3af171c50873b654e97673b3401df7a11bc3ca43318a73e443bef421351149eb18ce2c0fb6da84b90d2550b709bb72e) (by decide+kernel)

private theorem _EHY:WideCovered band82 10822984 11482192:=PRB band82 Z1.f1255 10822984 11482192 (WB 206367807640 16 0xefaa1b83b8c5652bebcd143bea86c798b0ea84eae9360efaa1ab196c1d27f6b7c9c3aea86945fb0059bcad517febaa1a29d2be5822eb2c23baea8680fc2f258faac0f9eeb9a19c474baa7566adbab7ae6865a03ae52708aacdbdeb9a190776b7eeb9ea8b333ae68628702da5786a98bdce79a1856d8b53e756a3abaf9e6860bb8ace2a04a849fae79a180628b22cc0e9ea42b9e685f78d2c32f92a7081ae78a17904aafb3e86999ca79e285cbba2baf630a5c638) (by decide+kernel)

private theorem _EHZ:WideCovered band82 11482193 12553408:=PRB band82 Z1.f1256 11482193 12553408 (WB 240727579800 16 0x83f50c60222c896d7dfc66041fa85ec2c159c7dfaf92b7a0fb42d6fa4a8c21bb7a11fd03da15859351d82bcbbc71c81ed0a81b9281311ddd429dc0f6852bd313928aeae50d6a07b4279f289aa48d37002f303da12d01c4cd4038b6bf9881ed08d0d1a6c0e83dabedb40f683c03393cf15dad0ef51e7741d88ae691062b65f3e8f3ba0e8a7533fab54b2590377dd07282699b8921d8dc093bee838aa90cb9d08ac45c8ddf741c2c2264b954360ec64efaa0df38631c9d90afd541) (by decide+kernel)

private theorem _EIA:WideCovered band82 12553409 13871827:=PRB band82 Z1.f1257 12553409 13871827 (WB 240761201816 16 0x8d0684c5ccb41ced63f4eab4e2c1a108240ce4ea09ed268f28b0283b39a0330578f7449c462c0a0d6dca0ba1bcfccfe5308902830f29c2aaa36af3a8d3e240a0b3e10c9bbaa0acd616d8902829d583247078a7307e361c0a09ab35487b8858caddab86fe8240ea01fe6fc1f266f2a1bfa0898b94788efc6c859e886fe82081141cb94dd71c601e13fa079f37c6cd61b4c5d62684fe81d57cc19f9578f12511613ea06f9dbc63760c2c3526484fa81a9d8817fe2e8708420e0bea065479c5ca1b00c0cea1) (by decide+kernel)

private theorem _EIB:WideCovered band82 13871828 14448635:=PRB band82 Z1.f1258 13871828 14448635 (WB 240761201784 7 0x4e8341c6770a1687a9b71dfee740a0daa2c92db968bb66c35361d0915ee0a5d6e4cd9f4389b0e8407e3a5447901ec592c4c89427c4582c4628eb5dc1da5c4a131c5f1393ee93ac5d2d2e1d08a563896a5fa0d4ecb4) (by decide+kernel)
theorem covered82:WideCovered band82 (AX band82) (tail band82):=(_Q1 band82 9174960 9504564 14448635 _EHU (_Q1 band82 9504565 9834168 14448635 _EHV (_Q1 band82 9834169 10163774 14448635 _EHW (_Q1 band82 10163775 10822983 14448635 _EHX (_Q1 band82 10822984 11482192 14448635 _EHY (_Q1 band82 11482193 12553408 14448635 _EHZ (_Q1 band82 12553409 13871827 14448635 _EIA _EIB)))))))
def band83:Band:=⟨10,71,2817,3274,30005213021045303⟩

private theorem _EIC:WideCovered band83 9306031 9638770:=PRB band83 Z1.f1259 9306031 9638770 (WB 206367876248 16 0xd34a390e12b07484352626e5a69470da6e60b1e9a64b08db4d28df204cc1a8d1cc9387d69a51baebc98a0e938921fbfcf3a38b1522c3eca8f239d059e746f0584552b5e5a45f51b3ce8d84812a1e4693489604e79d1a87735395ca1590dacdcf3a344eaba667e80b211321965464e7373fda8e9240e1532ca8c6301c7a46ada47f38c6595186d440ecab0238f95dccb2a37299eae596b051e893f965471af9e58e516863bcd8f2ca8dffdeaad9f41847511365951b6d4f14eda1a08e50ea) (by decide+kernel)

private theorem _EID:WideCovered band83 9638771 9971510:=PRB band83 Z1.f1260 9638771 9971510 (WB 1306953245848 16 0x6cda886ef7e12d0e064c139b76ed442c652098d43f25f57ebb76a212a4d84ce94172f097cd9b510f8c202465b0a9733826cda8877ec8123826ccb7122b66d443829a09286de25a4429a34a2237e7043266ef2c7f9ad1a5111aaf4217ed5695ee9168d2888c64a10b8af2caceaa356b46b9cfe58b3bd92553061ab5a35930fad61618929f5b8d5ad1a16155623d41394a9a06ad68d0a1d8bb24c59ca2c3234694744c396034118a501ca1a34a39f21f30694be3276bd6d1a51cc8b018400ef09364af) (by decide+kernel)

private theorem _EIE:WideCovered band83 9971511 10304250:=PRB band83 Z1.f1261 9971511 10304250 (WB 206367774872 16 0xdf6a33c1b92e17364e9d7d6db519d60a96a9e7273a6ff6da8ce3ac4b33b57393107b6d466f9a257d19a9c4747db6a335b2d2b6ef4cdfb056db5199acc95802e26e933b6da8cc2d24aa794f36a723b6d465cfaa53f4e79b0255db6a32b17929b5db4d588cedb51948cc9472916697f776da8c927d4a31829341d41b6d463e21a519cc399bd64db6a319f0d2887b1ccb613edb5188816948144a646baf6da8c13944a7836331935db6d45f36c25458f0987873) (by decide+kernel)

private theorem _EIF:WideCovered band83 10304251 10969731:=PRB band83 Z1.f1262 10304251 10969731 (WB 206367774872 16 0xe79a37ebb55f06d7d3b141f3cd1bea8cae4c63a9b002f9e68dee5f56ae1db4c3b25cf346f72aaafe08ca57b1ae78a37702d56031dd26c50f3c51b7d86aa7d9aa90d8a39e28d9b8e54e8d1347275fcf146b8cf2a43698a2f137e78a35115951ba1bd1275f73c51a1db2a88acda86b11b9e28ced8054166cb42139dcf1465bfdaa16a54a06755e78a31584d534cf1cfe26e73c517a998ab0e08a7c89979e28b81dc54fb0433cffd9bed4679c7a5982f09ddd73) (by decide+kernel)

private theorem _EIG:WideCovered band83 10969732 11635210:=PRB band83 Z1.f1263 10969732 11635210 (WB 206367774872 16 0xf3ba3d7a2d926d97d8c50577dd1e7f36c72ca7ac39e4bbee8f1e4e627f91b608a33df7478d5530c9cccafa2a1efaa3c5a21825ba5d7801477d51df682bf6fe6ab976c3bea8ee1ea5f00fb35b7671df54762c22f18818ad18bfebaa3a9a017540cbd63b2375d51d14b2b8fb45aaf4f3faea8e89575bc728b5662add754746662d6efe4aa8eddeb9a39cde168f3f1d4f63275cd1cb06eb32e50aa527b7ae68e3d995915923514ee9d73470f012c37c50a804fb) (by decide+kernel)

private theorem _EIH:WideCovered band83 11635211 12716615:=PRB band83 Z1.f1264 11635211 12716615 (WB 240727547032 16 0x85fd1dae345d99a5fc20a4785f51d17535aedf9ec0c55683f51c640057c3fbdbf806583f51bec4a556253cbe3b7483f51bc1c952ffa9bbcf68483f51b42e651814cabbb19283ed1aa7384fdbf09ba6ca283ed1a0cbd4f714f8b927b081ed191beb4ecf1d7b7e2bf83ed17b22f5069d56b69dcd79e517efad35aad95b558dd79e517cbf83501d84b4b66479e517b5d03460013b413ec79e517b56733cf352b3717479dd1797c833456b1b2cefb79dd177a8c32c2c70b22c83) (by decide+kernel)

private theorem _EII:WideCovered band83 12716616 14047576:=PRB band83 Z1.f1265 12716616 14047576 (WB 240761169048 16 0x8d0a8e47374a3fd55feb2cac4685469ce8e44a7307b54519a341a3283b91e3786fba79eed160d183245cd741bbcd28a848b068ba17d65ffd5ade8a2ca458345ac2cd2be80deb40028e2c1a2c32cf9424cf539d77651205159ff9495be588cd76c189028a9e3124520c93e618e7c481453a52720a8ec9b2bb37a1c0a2925c78f575ecb934fdd0e05144a4047455634c862fc86fe8a115da376ce39e38f06437f44f9a531a67f9cb17646a13fa2766790cae7d2389285509fd139324c60bcb80c34f39) (by decide+kernel)

private theorem _EIJ:WideCovered band83 14047577 14629870:=PRB band83 Z1.f1266 14047577 14629870 (WB 240761169016 7 0x9d0a8d5b9a0c061f6edf3bee9d0a8cabfc8c6045fdddf6fd9b168d5deb2bb17c24dcb20c9b168c68928b13c1cbdb6d1b99168c5b03082e7932da282a97128d26cb4a0e9e31d8e33997128c1a14288af610d79e48) (by decide+kernel)
theorem covered83:WideCovered band83 (AX band83) (tail band83):=(_Q1 band83 9306031 9638770 14629870 _EIC (_Q1 band83 9638771 9971510 14629870 _EID (_Q1 band83 9971511 10304250 14629870 _EIE (_Q1 band83 10304251 10969731 14629870 _EIF (_Q1 band83 10969732 11635210 14629870 _EIG (_Q1 band83 11635211 12716615 14629870 _EIH (_Q1 band83 12716616 14047576 14629870 _EII _EIJ)))))))
def band84:Band:=⟨11,42,4409,4781,9133855046139245⟩

private theorem _EIK:WideCovered band84 5504971 8795855:=PRB band84 Z1.f1267 5504971 8795855 (WB 206366726296 16 0xbadd63e7c3988cae8636cfbadd637aa392fdad85bb34bacd630fc38e618c853f98b6cd629b4389bb8b84c3fdb6cd621a7b85045a844862b6cd6189cb80362983ccc7b6cd6199a37b441883512cb6cd623f9b7504f782d591b6cd61e24b71d5f68259f6b6cd617c3b6ec3b581de5bb6cd610b136bd5548162c0b6cd608b13690e9380e724041d4058600e6cc2806b89041d40155802c1517e7d1d041d40154802bfd07aa044041d40152002bc7072e692) (by decide+kernel)

private theorem _EIL:WideCovered band84 8795856 9555290:=PRB band84 Z1.f1268 8795856 9555290 (WB 206366727320 18 0x346f5a94e6ab04e5d239ab5a31abdce7575f92d90d623d20d418bceb2163e47ef76e716b40915302b6ae3b9edf0bb5a27967fa5bb51be1037ddad05733f552da8d74e6beed67c2d1f76384c67ca55f76b3a148f99286631f6befbb59ca9e7bd87911804297ddace7d13d8b2388b8679068d405808074773c5856f02b6a02c8c03a275a284ea2eb759524e7748dcb1238e375bac9acb3b420c488a0d6badd6451c1d672f1c4129ddd6eb26550e99d18a1ea682eb759270c7433ba30e5c0b75bac888f39d149086b26a) (by decide+kernel)
theorem covered84:WideCovered band84 (AX band84) (tail band84):=(_Q1 band84 5504971 8795855 9555290 _EIK _EIL)
def band85:Band:=⟨11,43,4316,4758,9249793454189249⟩

private theorem _EIM:WideCovered band85 5636042 8967684:=PRB band85 Z1.f1269 5636042 8967684 (WB 206366726296 16 0xbaddab5aab98165e88d604baddaacb3b9214ed8858e1baddaa3d838d0a6c87dbbebaddaa886386af5b875e9bbaddaa9efb80b50a86e178baddaa30437c32d9866455badda9c3337866d885e732badda94793741f57856a0fbadda8bdc36f904684ececb6dda825936aeef5846fc9b6cda789ab6775e483f2a6b6cda6c74b62af83837583041d8069700e482282f860041d80197002b7918103d3041d80195802b6217d1abb041d80193002b2f075488b) (by decide+kernel)

private theorem _EIN:WideCovered band85 8967685 9736525:=PRB band85 Z1.f1270 8967685 9736525 (WB 206366727320 18 0x348f6f06b2a699abd29229ba47b73af85317bcd939707d22db7170aa220d6494e60e736d711853915eee4689ef39f6d14da94e24d5215069a4db0fcb150515198fadeec2fdb02bc9f1b24c4759d4e176d7db84f73dd2238da1b0bb6bcfa07ad046f1b72c77ddb5d82a3cff8f78d3c40beedae3271e430b3465f8e5f76d6d438f065d9a3107e6fbb6b63407731bab1789ad7ddb5b5553b3d1f48b47b3beedad3c81d71569c565485f76d66518ea2024a2935b6fbb6b14a07458f4313a0977dbb57c0b39df460895328) (by decide+kernel)
theorem covered85:WideCovered band85 (AX band85) (tail band85):=(_Q1 band85 5636042 8967684 9736525 _EIM _EIN)
def band86:Band:=⟨11,44,4228,4735,24716017786407410⟩

private theorem _EIO:WideCovered band86 5767113 9139513:=PRB band86 Z1.f1271 5767113 9139513 (WB 206366726328 18 0x2fbb7cc8b2e5db8a316ea737ddbe695b72303308af68ebeedf2d36b8cc477c53bf1df76f9257dc39c03a27e4e6fbb7c71eae09e0db12f51d7ddbe278a6fb65ec88fbe3baedf0a71b78e3a5c43e9c5d6ef7f6e5b92ad2a1ffa36eb77bd6b2db506d30effc575bbdf7366d01228870137baddefedd36329a3c341465d6ef7af71af1de9a180f86eb77b6d6cd221fcb0b0a6c0d5b8360606b1ac485068b06adc077700e2641c243f00346e014d0022928a0e2a2812b70074800ab402ff2a66083b8039d005540077aa84) (by decide+kernel)

private theorem _EIP:WideCovered band86 9139514 9917760:=PRB band86 Z1.f1272 9139514 9917760 (WB 206366760088 16 0xd27de2e3d54c0483a5d550349f785369524a2ed9657ead27ddf26b948aaef2556a5349f76cb9f5394bab945d3fd66dcdd5395db62aa4d7fa34a37746774d57709926292ce9dd9c9f12441e224594f73a776444e475d9079067e7c2fddb5ee0f2dd61a3daa470bf76d3413c483f68eebe6c2fddb0d94efac65639b4ef0bf76b2853b891748dee90c2fdda7e48ec6628e35bf96fbb768dc43ab9b828cf13abeedd9ec58e96330631ca42fbb76675339f63608bf3e5) (by decide+kernel)
theorem covered86:WideCovered band86 (AX band86) (tail band86):=(_Q1 band86 5767113 9139513 9917760 _EIO _EIP)
def band87:Band:=⟨11,45,4142,4712,9607988735631318⟩

private theorem _EIQ:WideCovered band87 5898184 9311342:=PRB band87 Z1.f1273 5898184 9311342 (WB 206366726296 30 0xc2fe3b79d39ac1bb8e146ec2fe3aef0b95d8ab8d943cc2fe3a4f93900bfa8d1409befe39a8138a2c198c93d6beee38ee1b83a9d98c13a3beee38304b7d84088b9371beee3830b37842788b133ebeee3881ab71f9178a930bbeee37edab6ce9f78a12d8beee3759036843068992a5beee36c04b63e526891272beee361d235f8dc588923fbeee34b7eb515b9488120dbaee33ef834c97948791dabade331f7b473f748711a7bade333613439604869174bade33ac5b3dc1b4861141bade3384ab3a8b4485910fbade32db3b36f1d48510dcbade321d5b333af48490a9bade3162db314174841076bade306e3b2d9d54839043bade2f6eb32c18d4831010b6de2e137b289634828fddb6de2db7032505a4820faa05fe004c58077d93818f78063e002ef8044222810f4506de00201802a4c1800edf054e00209802a2d07e0e14041e0020a002a1107a0c7d) (by decide+kernel)

private theorem _EIR:WideCovered band87 9311343 10098995:=PRB band87 Z1.f1274 9311343 10098995 (WB 206366760088 15 0x35a38a8a1b536999b9a1933d69e291821496142a6463375a789fc75519e699981868d69e26cc31464a3a25c600b5a7893b4e514d62796179cd69e220c61471945a545cdb4ab88db3a4aaecf59416d1d2ae1ee0752efb8124c59af4ab87976b482aeb3921605c70e1f2084f0ff04a4456830bf87b3eb3bdadf290956dc2fe1e7660edac2464054eb0bf8784ca3aee0718f9507c2fe1e1d2ce9d90823c53570bf8781ac3a07cf08e94a2) (by decide+kernel)
theorem covered87:WideCovered band87 (AX band87) (tail band87):=(_Q1 band87 5898184 9311342 10098995 _EIQ _EIR)
def band88:Band:=⟨11,46,4060,4688,9847300479172028⟩

private theorem _EIS:WideCovered band88 6029255 9483172:=PRB band88 Z1.f1275 6029255 9483172 (WB 206366759032 38 0xc70e6188e1d0731590b3a4c30e6121f9cccc259031e9c2fe60c131c9aaad8fb02ec2fe605c41c68a7d8f2e74c2fe608441c28e9d8eacb9c2fe606285bfd6058e2afec2fe6015a9bd704d8da944c2fe5fb959ba62f58d2789c2fe5f649db7f37d8ca5cec2fe5f0aedb580658c2413befe5e9d49b2444d8ba258beee5e38c9afb64d8b209ebeee5e5f01ac8d248a9ee3beee5e7599a9efac8a1d29beee5e2a7da814ac899b6ebeee5dce09a58edc8919b3beee5d77a1a3b40c8897f8beee5d19e9a1decc88163ebaee5ca3cd9f36d4879483baee5c2f899d58148712c8bade5bfe099b5e2486910dbade5c27819882e4860f53bade5c3a45967e74858d98bade5c07d5949004850bddbade5ba235931254848a22bade5b365d9207a4840868bade5aa9099025b48386adbade5a13f58f4e548304f2bade595db58eafe4828337bade58c9718cf60482017dbade5840358ce534817fc2bade576a158d8fd480fe07bade56c8458cdd5c807c4cbade544e159111e47ffa92b6de55a03d82fb6b7f78d7063e404a0806e5927ef71c066e4029c003b1c17e7561064e4011c4014cc87c6e76) (by decide+kernel)

private theorem _EIT:WideCovered band88 9483173 10280230:=PRB band88 Z1.f1276 9483173 10280230 (WB 206366760024 15 0xdaae6feb0951ef4c9cdd26daae6e73714c845c9bd9b0d6ae6d1e6149b4849ad63bd6be6b282d45217099d2c6d6be6a8dc141051498cf50d6be6868c942a92097cbdad6be64f43944a12896c865daae4f6f65593e7a95c4f0d6be61afe52bbabd94c17ac70e632378f2c40893be04c70e62bb70f0e630933c4ac70e62b70ceea0cc92ba8fc70e629268ecfcd09238d4c70e623b4ceb5fd491b71ac70e61e064e9b82491355f) (by decide+kernel)
theorem covered88:WideCovered band88 (AX band88) (tail band88):=(_Q1 band88 6029255 9483172 10280230 _EIS _EIT)
def band89:Band:=⟨11,47,3981,4664,10107399419212619⟩

private theorem _EIU:WideCovered band89 6160326 9318975:=PRB band89 Z1.f1277 6160326 9318975 (WB 206366759032 46 0xc2fea28b3db2caef8e323fc2fea26d85b007878daefcc2fea21569adb0c78d2bbac2fea1b895ab570f8ca877c2fea15621a8f9b78c2535c2fea0e2b1a6172f8ba1f2befea06b05a361978b1eafbeeea02c21a0d9d78a9b6cbeeea03eed9e3e478a182abeeea05b459b8acf8994e7beeea0020d99bbe78911a4beee9fa1f197f16f888e62beee9f2f6d95aeb4880b1fbeee9ebafd93e34c8787ddbeee9e38199218a4870499baee9da79d904fb4868157baee9d96dd8e852485fe14baee9d88f18cb82c857ad2bade9d7f598ae4ec84f78fbade9d7c918905a484744dbade9d2e4d87be2483f10abade9c9f4186f7bc836dc7bade9bf1b58645ec82ea84bade9b094984df14826742bade99f3a984d32c81e3ffbade98cb0d85664c8160bdbade976c6187161c80dd7abade95fb75865cd6805a38bade95f97d7cc79d7fd6f5b2ce9b61d5657f3c7f53b2b2ce9b306964d4547f1211b2ce9afbd964292c7ed06fb2ce9ac3b1637dd47e8eceb2ce9a876962d21c7e4d2db2be9a465d62260c7e0b8cb2be99ffb96179947dc9eab2be99e3ad60cc2c7d8849aebe99dbb95ffc3c7d46a8aebe99dabd5f05c47d0507aebe99d2995e3f1c7cc365aebe99c9595d810c7c81c4062e80503806cef37c4023068e802d3c03a5427bbce005de801c100211317ab65a041e8013780146b8769c45041e80134c0145006e681a) (by decide+kernel)

private theorem _EIV:WideCovered band89 9318976 9923823:=PRB band89 Z1.f1278 9318976 9923823 (WB 206366760024 16 0xdabea6a1d1493176976cefd6cea96a9121c12d96666acb1ea6ee40f08e6c955fe5cb1ea68898eed14494dca2cb1ea62008ed10ac94595fc71ea5b404eb4bbc93d61dc70ea543dce980b89352d9c70ea4cebce7ade892cf97c70ea4e0b8e5d0b4924c54c70ea4bcace42ec491c912c70ea45b30e29bdc9145cfc70ea3f4f4e0fd9890c28dc70ea39190df862c903f4ac30ea32960de0a088fbc08c30ea2bb4cdc87388f38c4c2fea270fcdafbe48eb581) (by decide+kernel)

private theorem _EIW:WideCovered band89 9923824 10461465:=PRB band89 Z1.f1279 9923824 10461465 (WB 206366759960 8 0xdabeb5db115781ba7e84676b3ad071a5469109e9a93daceb37afd4bfd6a76503b6b3acc6eb51e3819c8d89daceb17809429f366e1c136b3abfb5e5017c69a807fdaceae07793f83c665e7eb6b3aad7d65055e7987375) (by decide+kernel)
theorem covered89:WideCovered band89 (AX band89) (tail band89):=(_Q1 band89 6160326 9318975 10461465 _EIU (_Q1 band89 9318976 9923823 10461465 _EIV _EIW))
def band90:Band:=⟨11,48,3905,4639,10484772002761674⟩

private theorem _EJH:WideCovered band90 6291397 9112945:=PRB band90 Z1.f1280 6291397 9112945 (WB 206366759032 49 0xbefee2d7a59cb71e8b0d71befee272219a1c568a88a7beeee27c899769d68a03dcbeeee286d194f17c897f11beeee25a29929d3488fa47beeee1ec7190bba488757cbeeee185058f9f5c87f0b2beeee100a18dccdc876be7beeee06b0d8bfb7486e71dbeeedfbe7d8a28ec866252baeedf8bf98854ac85dd88baeedf6fad86799c8558bcbaeedf2a5d857f2484d3f2badedee8b584487c844f27badedebfb1828a2c83ca5dbadede92e580c914834592badeddc7298036ec82c0c8badedcc6c57ff414823bfdbadedb77dd8063dc81b733badedafa5974eafd813268baded9ce0d75f1d580ad9ebaded7b1e978ed8d8028d3b2ceddaaf56038ac7fa409b2cedd7b395fb29c7f61a4b2cedd42155ee16c7f1f3eb2cedd0c215e5de47edcd9b2cedccb795d89b47e9a74b2cedc8d555d090c7e580fb2cedc4a515c8cbc7e15a9b2bedbf9895bb2a47dd344b2bedbc0015b39fc7d90dfb2bedbb4995a599c7d4e7aaebedb982959e49c7d0c14aebedb85b9592cfc7cc9afaebedb6f3d5889847c874aaebedb4cb5581ff47c44e5aebedb45d95724ac7c027faebedb1f1156c0447bc01aaebedb1e2955ad1c7b7db5aebedaf249554dcc7b3b50aebedabe3554fdcc7af8eaaebedacd9553b2647ab685aebeda918d53685c7a7420aebeda3a4d52d0347a31bbaebed9d17d52cf8c79ef55065ec055cc06b96b79acf005eec030ac039932796a8a063ec01e08020a7978e5bf041ec014cc014128709916) (by decide+kernel)

private theorem _EJI:WideCovered band90 9112946 9656858:=PRB band90 Z1.f1279 9112946 9656858 (WB 206366758936 16 0xc71ee814e1cb03349ad0d638773d10ae3fd164b553f1c3b9e1ee7109f524a10b8e1dcf039b80f5091cbbac70ee71ae5bd84048a377e387735810dd43b24308971c3b990306de06f207ab58e1dcbb4836a2b68fb890c30ee56019b207d4799e2e17f72762ed76dca3abbef0bfb93f9d6ae57f1c546185fdc9faf350db28da566c2fee499e1a5fdb46904de17f721b94d1e8c2326f470bfb8f41b686f6f182e0d85fdc6b2433e81b8b923c) (by decide+kernel)

private theorem _EJJ:WideCovered band90 9656859 10574711:=PRB band90 Z1.f1281 9656859 10574711 (WB 206366760024 16 0xdedefd44895ea8e8a15b77dedefb742557d090a051e2dedef9e0b55334689f484ddadef7c5994cd3a09e3eb8dadef6ce6d4684109d3523dadef6b4394369d89c2b8edadef5338d4022209b21f9dadef349053def909a1863dacef1592540e150990ecedacee1d3154e8246980539d6ceee3b5520993596fba4cb1eea5de8ee87cc95f20ecb1ee9f144ecc034956d44cb1ee97fcceaf7cc94e879cb1ee90b0ce92ba49463afcb1ee89250e75a0893dee4) (by decide+kernel)

private theorem _EJK:WideCovered band90 10574712 10642700:=PRB band90 Z1.f1279 10574712 10642700 (WB 206366759960 1 0x37b7bfa6d1598707a2650c) (by decide+kernel)
theorem covered90:WideCovered band90 (AX band90) (tail band90):=(_Q1 band90 6291397 9112945 10642700 _EJH (_Q1 band90 9112946 9656858 10642700 _EJI (_Q1 band90 9656859 10574711 10642700 _EJJ _EJK)))
def band91:Band:=⟨11,49,3832,4615,12727310395711925⟩

private theorem _EJL:WideCovered band91 6422468 8898293:=PRB band91 Z1.f1282 6422468 8898293 (WB 1306952128632 55 0x17aef23296584901387c6f55ebbc8a7de60d468e1d02897aef21f58d819e8b86ba505ebbc85161603b08e18cff57aef2081697f590b85adab5ebbc800145fc59ce149d657aef1f9e117dca9b84a1065cbbc7c9495f295ee106ad17aef1ded517e076b8394615ebbc72ac35f9d84e0c38397aef185e91863b478287bc5cb7c74a215b001d20805a572df1c67c56bf3a4817b175cb7c6d788598e6ba03d31572df19c1b1681dae806e7258b3c7bdee564a90dffa08162cf1ef5a15825e37fa4f758b3c7bddf55c510dfd873562cf1ee221562b037f1ea458b3c7aa00556dc8dfb6ded62cf1e6915553f4b7e985258b3c7887c552928df954a162cf1dd501540ac37e11ff58b3c7605154dc6edf73b5962cf1d2de553394b7d8bad58b3c739b354aae0df5220d62cf1cc5a1521b237d055a58afc7289c54632cdf308c562bf1c7ce551009b7c7f0858afc70e5e5440a6df0ef7962bf1c09cd50872b7bf8b558afc6f54c54046edeed6315abf1b9a494fa47b7b726356afc6d5d753d062decbce75abf1ac7b54fddcb7aec1056afc6967453f1eedeaa39f5abf19ccd54fe6d37a65bed6afc642aa54194ede88a575abf17ddfd51aad379df6cd7afc55b2b55372d5e6710d5abf1a010943a6bc79591a56afc66b1450ea251e457c15abf19485943c81478d2c756afc633e95103f91e23e795abf1a20454447cb784c7556afc68063510040de0ab8356af19c2ed4428b378094bd5abc6664650fe8eddf9edf56af194f91442e6b77c622d5abc63ccf5123d4dde923b56af18b9a14470a37782f9d5abc60f245143ccddd859409ef00aa700ccef2773fd00293c00ce900e3765dbf298087f001638013d8072ca12) (by decide+kernel)

private theorem _EJM:WideCovered band91 8898294 9448477:=PRB band91 Z1.f1283 8898294 9448477 (WB 206366758968 16 0xc70f2833d1aa681640b0771c3c9f1766a06d38fa5cac30f27408da51ade3c7de30c3c9af6c68a14b8e9926c30f2682219fa05e384b4f0bfc9a3f06716f98d8c81c2ff26802999fcee3418bf0bfc9838065e7c78c7fdcc2ff25a45d95e7ce2fe6270bfc949e664f0d28b7336c2ff24992591542a2bb392fbfc8fee863b51e8a6692beff23c4e98d20922780fefbfc8f101629efa8959edbeef23ab9188c092234e6afbbc8ea1f6182dc884d48) (by decide+kernel)

private theorem _EJN:WideCovered band91 9448478 10067433:=PRB band91 Z1.f1284 9448478 10067433 (WB 206366759992 16 0xdedf26f9194a0eb1333bd3b5be5d98da41ef2e6245133cbcb57da3b43d64bc24fe597966b6a75905496fe4dcb1f2c4048e8fc392ceff7963e5823e1ce559a57c6a32c7cb00ae39437f4ab5ab658f95cc7671d10494e503cb1f2b1ca8e1e64128bd61963e5537f1c04a424f617b1c7ca899937acab49a905e38f94cd426e722892cbb9c70f292db0db682d248acd8e1e527389b3078a46fc531c3ca43e835f3de489c6163879455cc6b54da90b26f) (by decide+kernel)

private theorem _EJO:WideCovered band91 10067434 10823935:=PRB band91 Z1.f1285 10067434 10823935 (WB 206366792728 11 0x1c5de4645796fbfd694a3ff8bbc887f0ad0842520e2d6f7790711b57be66a30fb5deef1fc164abe27d440621bdde3f8ca550dc6e83d9af7bbc7bd88a9865bcff4e3ef778f0c295203c49edd22deef1d2202a24e8d3ba0fbb5de3778713f3f2e730f5f6b7c68bed27b7ee4ddb996d6f8c4fab4fd1439aaa8e) (by decide+kernel)
theorem covered91:WideCovered band91 (AX band91) (tail band91):=(_Q1 band91 6422468 8898293 10823935 _EJL (_Q1 band91 8898294 9448477 10823935 _EJM (_Q1 band91 9448478 10067433 10823935 _EJN _EJO)))
def band92:Band:=⟨11,50,4170,4590,11192912953514045⟩

private theorem _EJP:WideCovered band92 6553539 8779354:=PRB band92 Z1.f1286 6553539 8779354 (WB 1305878354040 16 0x5f77b177319a073285f65a5d77b0f74d98f272856e7f5d77b09d8596997284e6a55d77b0701595c3c2845ecb5d77b01e3d95591a83d6f05d77b05a3992db1a834f165d77af784193d33282c73c5f77ac2c3d99ecba823f61dd77a66949a198d481b7875d6fae31fd8272e3812fad5d6fad1841841aeb80a7d25967b0d1c5709aea801ff85967b0b8556ff2327fdc0b020fa031d006fcf17f981e0247a00c0c0152d07d78b4020fa00bf001512874fb0e) (by decide+kernel)

private theorem _EJQ:WideCovered band92 8779355 9335808:=PRB band92 Z1.f1287 8779355 9335808 (WB 206366726200 16 0xc30f68ebe37d50ac73a006187b43f89bafb0e37b0970bfda38ecdc2c2d1ac89785fed145a6d59f28cdc71c2ff68350366a01462a4b617fb3dfc1b13b822f32f30bfd9cb72d72f751689c57dfecd4256b0f468abd07beff66048b542fc451a96df7fb2c689a6ef0a26b54efbbd97b06d24f95124af17ddecc521689dcc889d9ebeef659fe34084c440ae25f77b28d499ed72a1e37a6fbbd920f4cec0150e0c1f7ddec77e266d052867e35) (by decide+kernel)

private theorem _EJR:WideCovered band92 9335809 9892262:=PRB band92 Z1.f1288 9335809 9892262 (WB 206366726168 16 0xcb2f6f5073ead0096f1a6cb2f6ec1abe2d999669cbcb1f6e4aa3d92db95e1f1cb1f6e7413d1a1e955a17cb1f6e022bcb44694d23ccb1f6d7c93c38d3944a62cb1f6d0283bd14093c288c71f6c837bb68b5933aadc71f6bec3bae6c492b2d3c70f6b5ee3a79d2922af9c70f6b8bbba0a5e91a31ec70f6b5e8b99985911b44c70f6af1939454790936ac70f6a7f9b8f0c0900b8fc70f69f62b884998f83b5c30f6975bb82d838efbdb) (by decide+kernel)

private theorem _EJS:WideCovered band92 9892263 10866056:=PRB band92 Z1.f1289 9892263 10866056 (WB 206366759992 16 0xe2ff64dd198a7d294b9b11c5fec906c306a59292f7538bfd8da9d5ec68951d70fef7fb1215cb982dea29e6adeef613bb96d7ca9431d6dbddec06732cb5b7a81fc077bbd810fe57e2604fb7a66f77afbf88ae9f729e5f97deef5e62d15991ad3a9fc5bddeb9ff7aae23327100bb7bbd6d8e656e5204d983cef77abe074b0f65d9a20c4cf2f58b89102ce113222219e5eb0f24a01c5a26224d73cbd60e153fbd7d4c00ade797abf68a7e558c977981) (by decide+kernel)

private theorem _EJT:WideCovered band92 10866057 11005170:=PRB band92 Z1.f1288 10866057 11005170 (WB 206366759960 2 0xe6ff677c95a1688e9fb3cb8bfd9859b657d32a6dd3d) (by decide+kernel)
theorem covered92:WideCovered band92 (AX band92) (tail band92):=(_Q1 band92 6553539 8779354 11005170 _EJP (_Q1 band92 8779355 9335808 11005170 _EJQ (_Q1 band92 9335809 9892262 11005170 _EJR (_Q1 band92 9892263 10866056 11005170 _EJS _EJT))))
def band93:Band:=⟨11,51,4095,4564,11589063337802189⟩

private theorem _EJU:WideCovered band93 6684610 8407953:=PRB band93 Z1.f1290 6684610 8407953 (WB 206366726264 16 0xb2cfa4031ad33969009723659f486c25a1bcd2001b82cb3e91228b3d6023fe117d967d249216660ac7f7d7eb2cfa46a82cbab98fe719b659f4841459454d1fbd072cb3e8f67eb252de3f57b55967d1c28163e3b47e6abab2cfa33252c6f6e8fc4c11659f459ca58ade51f7855ecb3e8982ab0f8463ece535967d0f8f161916c7d57f5041f806ec80dcf26fa2688083f007da00ed0e9f22784107e009b4010d48bdbb8e820fc00d60014d50772c0a) (by decide+kernel)

private theorem _EJV:WideCovered band93 8407954 8900336:=PRB band93 Z1.f1291 8407954 8900336 (WB 206366726232 16 0xbeefa946b32b93f21f3bc2fbbea2c1cca3d4887458ebeefa7f7cb269f521af0b2fbbe9c7aac9233c8632cabeefa6176322d6f216a59efbbe932e0c868ec852005beefa3109320f322125a8efbbe844bac78c50840d41beef9ef9032066e20e0f7afbbe6ae46c9d2f882fa7cbeef9764f3256f4a09c46aeb7e87068bd6bb981e7b8b6cfa49ee2da53d2057956cb3e910dab625b88119a5b2cfa3e0d2d6dbb20353cecb3e8feaab52a90809043) (by decide+kernel)

private theorem _EJW:WideCovered band93 8900337 9463061:=PRB band93 Z1.f1147 8900337 9463061 (WB 206366726200 16 0xc70faf35bb7996dc8328ae387d759c5ba3dc63f6ecf1c3eb8a6adbd5971ea4a38e1f5b1246d253c8ec8eec30face93363cff471fc66187d61d25af2a4a36d8ab0c3eb0c78d62b7d1a599185ff5955e6a58f88ca365c2ffac336b4eb8c460d01e17fd5d529a55f4a2e42870bfeac420d19df9160e7f85ff54b126823fc8a7ddcbeffa99c533d02f44fa3d5f7fd461ed9c6bba25ac62fbfea267acd25cd11c36d7dff51bff660670885853) (by decide+kernel)

private theorem _EJX:WideCovered band93 9463062 10025786:=PRB band93 Z1.f1149 9463062 10025786 (WB 206366726168 16 0xcf2fb64623e9c1398fb3acf2fb5b90be25c39871d8cf2fb5286bdaeca97e875cf2fb4939bd36fe975f13cb2fb3f9b3cbde796d5b1cb2fb359bbc4324964c4fcb2fb2b26bbc63195c2eccb1fb2bd6bb309395398acb1fb27bf3ac27d94b028cb1fb1f75ba5f069426c6cb1fb16d8b9faac939d63cb1fb0dd7b9952e931401c71fb045e392e24928a9fc71fafa50b8c50792013dc70faf3de3859399177dac70fafb1a37eac990ee77) (by decide+kernel)

private theorem _EJY:WideCovered band93 10025787 11045724:=PRB band93 Z1.f1149 10025787 11045724 (WB 206366759960 16 0xe70fabc929965c0aa22d739c3ea9ebc635168a77897e30fa924658475a699974f8bfe9ef235ef5e9a5530ee2ffa7723173533291012b8bfe9a00b5b5c9ea32d85e2ffa52db565de52886b077bfe8fde858381aa107fcdeffa28f495c968a7fd4e37bfe831385657cc9ee273deff9ee88558356e773ebf7bfe69fd7571d889cbceae2ff8be1656a387a6ea89b3cfe6edd84056aa9a9761cf3f9b6058ff12966837ff3cbe6c1913f305b99849c) (by decide+kernel)

private theorem _EJZ:WideCovered band93 11045725 11186405:=PRB band93 Z1.f1149 11045725 11186405 (WB 206366759960 2 0xe70fae4c41af47deaac3979c3eb255668bab0a99e20) (by decide+kernel)
theorem covered93:WideCovered band93 (AX band93) (tail band93):=(_Q1 band93 6684610 8407953 11186405 _EJU (_Q1 band93 8407954 8900336 11186405 _EJV (_Q1 band93 8900337 9463061 11186405 _EJW (_Q1 band93 9463062 10025786 11186405 _EJX (_Q1 band93 10025787 11045724 11186405 _EJY _EJZ)))))
def band94:Band:=⟨11,52,4023,4538,12183682380187832⟩

private theorem _EKA:WideCovered band94 6815681 8273730:=PRB band94 Z1.f1292 6815681 8273730 (WB 206366726231 16 0xb2cfe6c9cabc94dbf1fa15967f3310d5db7e5f7e736cb3f97c1eae9396fb68b1659fcae5d5726237d6ee3b2cfe4e6eab8187be94b75967f224ad5b82d5f38fe6cb3f8e5c4ad7e12f93d07657fc6cfd569e717c590fb2bfe2ef6ab52acbe09ccd95ff1546d5a2ce5ef3896caff895a4ace7a2f7115f657fc3e6b5660837b433baebfe178aab2960bd7ee2d75ff06d15593655eae140107f01e4403695df4e5b6083f805500084f4795d06) (by decide+kernel)

private theorem _EKB:WideCovered band94 8273731 8593789:=PRB band94 Z1.f1293 8273731 8593789 (WB 206366726232 16 0xbeefde18231af87a0c85f6eb7f9c8a2bb3cd5829693b6dfe91c02d39152082ea6db7fa3192b47b4881c634b6cfe86a92d043920602fedb3fa01fab3a4ec813b4ab2cfe79d32ccdc4203d756cb3f9cf56b2c6e480b060b2cfe748c2c94f9201abaecb3f9d63eb1dd94802576b2cfe76f82c58b61ff8002cb3f9e36cb0e3187f9a8cb2cfe78dbac24221fd545acb3f9ebaab017d87f0fa2b2cfe780fabee8c1fb28b2cb3f9ca3eaf6f507e84b7) (by decide+kernel)

private theorem _EKC:WideCovered band94 8593790 9162785:=PRB band94 Z1.f1294 8593790 9162785 (WB 206366726168 16 0xc2fff048c3402978bd021c2ffefa47b3c03b8b4537c2ffeeef7b37d988aba4cc2ffee24c333a5b8a2f61beffed3d7b2f62a89a477beffec2f6b2b07789198dbeffebe98328e94888ea3beffec1333247ed8803b9beefec5cf31fd248778cfbeefec3ae31bf5786ede4beefeb519b199a88662fabeefea40bb180ff85d810beefe8fefb186e5854d26beefe73bcb17c5d84c23cbeefe4c8ab18458843752beefe10efb1ade183ac67) (by decide+kernel)

private theorem _EKD:WideCovered band94 9162786 9731779:=PRB band94 Z1.f1147 9162786 9731779 (WB 206366726200 16 0xcb1ff74a439b73eca3f61e58ffb5839ca82d64fcf672c7fd8940e3f81b26d1df963feafaf712a6d92de05c71ff4cc7b82a5fc9298de38ffa07edbde7664720c71c7fcf952dd2ff3227a8d8e1fe85546dca6490b25cc70ff3996b6906d4813b96387f98001b1d6723e72231c3fc9c9cd7ec9d1e233d8e1fe38776b48028e86b4c30ff1058354ac346fde4e187f819f1a775ba35c37f0c3fc1e90d23b7519cbeb85ffe1974685ee48c5b0b) (by decide+kernel)

private theorem _EKE:WideCovered band94 9731780 10443023:=PRB band94 Z1.f1295 9731780 10443023 (WB 206366759992 16 0xe2ffe581295b1d613eb21fbdffc5f06ab149fa790cef8bff7d2695821104e96b3f17fe9ce2cb412019c1792d33fdec008ff183136037b9e7fbcbdc9f98ce269db4f3cff7819d3eb3804cf5f4e797eecf747c36649960ffcf2fddbf3cf608e131ac2b9e5fbadc21e8439a612cab3cbf746ac3c8dcb4be0206797ee62567823c4973556cb2fdc7680eeacc52d54d9965fb833a9d961d2587e0b2cbf6ee273aaa944aca4c658fede768744ace9509ad) (by decide+kernel)

private theorem _EKF:WideCovered band94 10443024 11367640:=PRB band94 Z1.f1149 10443024 11367640 (WB 206366759960 13 0x3ac7fdfb4272d04fad74d8eb1ff62ff5bf5f0ab17c0fac7fd0c136c6aa8ab492fe71ff237eda49c86a8cd6f9c3fc24ec665acfa91d86e70fefcbbd8eb0c2a01ecb9c3fb955e617950a6f1dee30fecdd617dc2729770278c3fac8485d1aa6a4c635e30feafc8d6cf0968ec1878bffa7c1d59cf3ca29a8ce2ffe892756176ca8612e38bff9d51257bb9ea06ee4) (by decide+kernel)
theorem covered94:WideCovered band94 (AX band94) (tail band94):=(_Q1 band94 6815681 8273730 11367640 _EKA (_Q1 band94 8273731 8593789 11367640 _EKB (_Q1 band94 8593790 9162785 11367640 _EKC (_Q1 band94 9162786 9731779 11367640 _EKD (_Q1 band94 9731780 10443023 11367640 _EKE _EKF)))))
def band95:Band:=⟨11,53,3953,4512,26556557836811466⟩

private theorem _EKG:WideCovered band95 6946752 8079305:=PRB band95 Z1.f1296 6946752 8079305 (WB 206367876247 16 0xb2c802262e8552d4b5ed1f26cb2008479415582957b0190b2c801fd900556e1d3eaed5ecb2007b3be155541c7a751eb2c801d6190553ea6fe8bb96bae00938ea144ac5379e8acaeb802421b0512e72de689cebae063e744ce17342f95c3aaeb813ed1629dc9c2be45806bae055abe0b8240c2f8cfc8aeb819f468b975472be2263ebae02edc6c6bc64ca784356041800082d001afa67dff47410600012900039db177b6e304180002e0000834e3dca9c410600007f0001445872c6e1) (by decide+kernel)

private theorem _EKH:WideCovered band95 8079306 8366938:=PRB band95 Z1.f1151 8079306 8366938 (WB 206367774743 16 0xb2c8149bc95b993ffab5ab2c8148b855b074ff6521b2c814971559e82ff1ee8b2c81488a1594ed7ed8aeb2c814793958b727e9276b2c814765157e937e4c3cb2c8148e8956b687e0604b2c814760d56283fdbfcab2c814357d55e90fd7992b2c813e6e555470fd3358b2c8139541551ab7ced20b2c813382554fe9fca6e6b2c812c86954af07c60aeb2c81245f9547677c1a74b2c811e64d549ee7bd43cb2c8117e0554f497b8e02) (by decide+kernel)

private theorem _EKI:WideCovered band95 8366939 8708501:=PRB band95 Z1.f1297 8366939 8708501 (WB 1305879402584 16 0xdf7c06cc12ca1d2684e1955f740a5524b9d0a58455235d740a2288b9610583c8b15b6c0b36b4b2ab94833c3f5b6c0b4536b1f75c82f6075b6c0b3d44b194d482afcd5b6c0b2a1eb147708269945b6c0b15d8b0fb2882235b5b6c0afdb2b0875881dd225b6c0ae680b03b108196e95b6c0acd8eaff0008150b05b6c0aafb6af7798810a775b6c0a9238af2c4480c43e5b640a71e0aee1d8807e055b640a53c8ae98b88037cc59640a5574ae17187ff193) (by decide+kernel)

private theorem _EKJ:WideCovered band95 8708502 9283768:=PRB band95 Z1.f1151 8708502 9283768 (WB 206367774744 16 0xc7081a1a1d9f0a0c6d45c61840cd018ce264a3471170c206578a66939b191fa586103306ab2eef28c0360c2f819b1b1946d8c5bb77617c0caf10c999d62ba9f30be063ce464502314bc1585f03111fb206ba89d198c2f817fd518e52bc4a293617c0bae62c66abe22e2d30be05a92362f2531058857df02d087314099879fd0bef815f8858a0b1c389af5f7c0ad4cec459c61a1bb2fbe0511dc62ac9d0bf4f385f0256eb317f3e856e07) (by decide+kernel)

private theorem _EKK:WideCovered band95 9283769 9859033:=PRB band95 Z1.f1298 9283769 9859033 (WB 206367774776 16 0xcf281e4a99cdecd659bf672ca077c1f72b2d795e367cb281d84edc6de5e555bd72ca07565470e81794ca83cb181d7b8dbfa4ae50f8472c60749a86f221993b19ecb181cd901ba0c5e4c94b32c6071fee6dc7749298bac7181c1c91b3e08a4831231c606efc56c5504917fd6c7181b65f5adec9a43cd931c206e0106ad0909066f2c7081b85dda807823f6a031c206cbdd695cc48f4e0ec7081adeada38d223b06731c2069ea5683a988e352a) (by decide+kernel)

private theorem _EKL:WideCovered band95 9859034 10614068:=PRB band95 Z1.f1299 9859034 10614068 (WB 206367808568 16 0xe30815cedcad685ea1f534e3081567c6abeeb6a0dc50e2f814aca8ab89c89fc36ce2f813bba0acb6169eaa88e2f811aad4ab10bd9d91a4d33810da147e932a9c78c0d33810bf007d663e9bec4ed33810909a7c67f69b5fdcd338105fb07b5e1a9ad369cf38102b087a40609a46f7cf380ffad0794d6699ba85cf380fc246782704992e13cf280fb748772c8698a1a1cf280fad16761f8c98152fcf280f7fe67534d89788bdcf280f562e746d7496fc4b) (by decide+kernel)

private theorem _EKM:WideCovered band95 10614069 11548875:=PRB band95 Z1.f1153 10614069 11548875 (WB 206367841304 13 0xef281025717836bfb038cbef280f89767454c2af1fe6eb280eef2b70944eae0702eb180e54356ceb54acee1eeb180e170769df42abd53aeb180da1cb673346aabc56e7180d26f5647fa2a9a372e7180c9a396173a4a88a8de7180c82665f255aa771a9e7080c26445d6146a658c5e7080bc6045bba63a53fe1e3080b5dcc5a3358a426fde3080ae6e758d2fca30e19) (by decide+kernel)
theorem covered95:WideCovered band95 (AX band95) (tail band95):=(_Q1 band95 6946752 8079305 11548875 _EKG (_Q1 band95 8079306 8366938 11548875 _EKH (_Q1 band95 8366939 8708501 11548875 _EKI (_Q1 band95 8708502 9283768 11548875 _EKJ (_Q1 band95 9283769 9859033 11548875 _EKK (_Q1 band95 9859034 10614068 11548875 _EKL _EKM))))))
end
end AY

end SubmissionLower
end ProximityPrize
end
