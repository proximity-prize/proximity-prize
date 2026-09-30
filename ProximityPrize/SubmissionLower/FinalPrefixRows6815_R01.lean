import ProximityPrize.SubmissionLower.FinalPrefixRowsCheck6815
import ProximityPrize.SubmissionLower.CompactAllN6815
import ProximityPrize.SubmissionLower.FinalLedgerData6815
import ProximityPrize.SubmissionLower.SingletonData6815
namespace ProximityPrize.SubmissionLower.FinalPrefixRows6815
open FinalPrefixRowsCheck6815 PackingSemantics6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
def row0 (_ : ℕ) : Entry := zero
private def q0 : Array ℕ := natRow 13 52 0xd42707b7bb17fd42707b7bb17f754d35e31d6a5d15c2a1fd91fbb3ee607ae4100818049fd974d825923d02ac02d22d315d511c830000000000000
private def q1 : Array ℕ := natRow 13 52 0xd8623eb134125d8623eb134125754d35e31d6a5d580505c66311b57cbbe7ede83818049fd974d825923d02ac02d22d315d511c830000000000000
private def q2 : Array ℕ := natRow 13 53 0x1082113cf22f68841089e7917b42358471b28ce7608b0398e492ceddb843876bedf4f52552571ebe8a43c4315af7044ab4bbe3a593e0000000000000
private def q3 : Array ℕ := natRow 13 53 0x1987c193a11da7cc3e0c9d08ed3bc3cbd7173a3cf23faaf392adbd5bcc47a07429b800da13af52ca968c22b503ae70ac02245aec77c0000000000000
private def q4 : Array ℕ := natRow 13 54 0x2248f1c5b00b4e8923c716c02d39515cf615eca3486dbd011ce5259d6137ba3b4d3357a556a2dc33cc89a53fd347e13213ec0566bfde40000000000000
private def q5 : Array ℕ := natRow 13 54 0x2b24a2075ef98dac92881d7be635b304cd3aa3d56a9a062adfcb2c651d54d4a59fbf6f8f5446f5680cb9c5f3735ef5e2d283bc9b1e8200000000000000
private def q6 : Array ℕ := natRow 13 54 0x33f272421de7cccfc9c908779f32140b4e4edefbccc2e8becb12162ccd30e213373b87534473c122ece997bf3ad90e238fdfd46d093400000000000000
private def q7 : Array ℕ := natRow 13 54 0x3cb26275ecd60bf2c989d7b3582e747079529e166ee864bcdeb9e2f470cbe28413a79ef127293f646d19176d0e283f944bf3746e484ac0000000000000
private def q8 : Array ℕ := natRow 13 55 0x456472a2cbc44a8ac8e545978894b50948eb900a0e214eb944354b3bc07be177b63c75b326d76b1d896520d0e3b806510a0cf719435fdd00000000000000
private def q9 : Array ℕ := natRow 13 55 0x4e0552c702b2859c0aa58e05650accc873434a0a0a650a9ee225848c38feebab79b4b66d6c213b9bd9e5dbaad1ddeb51cb7ed4c6f72e8080000000000000
private def q10 : Array ℕ := natRow 13 55 0x569b42e5d1a0c4ad3685cba34188e59e269b810baaa89d4aeb7718f4b2fa197fd4bbf731eb650ba8c366c26fe08a363e0d4888b5b7c8fb00000000000000
private def q11 : Array ℕ := natRow 13 55 0x5f1f42fb988effbe3e85f7311dff063325114dff32ecc78a18b1b20d39909b87df93783e0e180fa7b9e8cc5ef81cac9fd15890b644ba6080000000000000
private def q12 : Array ℕ := natRow 13 55 0x6794a30a0f7d3acf2946141efa75268da369daf2bb307cc90b6c4b25bf3d1d1aea6af9485cca29a6b06ad2a60ddb2301956148b329abc60044cdb04fda86
private def q13 : Array ℕ := natRow 13 55 0x6ffb6311366b75dff6c6226cd6eb46ada1a527e64373bd07c3a6e43e43ff9e38f5427a50d77b59a5a6ecd54521c599635962b0ac669d2b86e2bc5755e326
private def q14 : Array ℕ := natRow 13 55 0x771224e4e69dcfee2449c9cd3b9f618da71299ea47ac7d54e02b9e4eb3c23c1f945beb2f52661acd214e83e4a8d260ccdcbc198be830a08c5edbbaf47c60
private def q15 : Array ℕ := natRow 13 55 0x7a4a4fce0c435ff4949f9c1886bf7142ab6ce1a56fc6e757cd2d0256ecfa43dba81bfbb9a5156701122fd99a529b4c0e1f63aeb0e20bc51214e0fd4e32af
private def q16 : Array ℕ := natRow 13 56 0x8223ef8ec331a28223ef8ec331a263c9a4d0a786a380b7afb27431af768ddc8c318cc76581af99b9af7946df68308929414638afeab019d71832f5810ac12b
private def q17 : Array ℕ := natRow 13 56 0x89f06f48ea1fe589f06f48ea1fe56b357ebf86a3eb88855464b2c3147e3ef4d41897cf6d291681ab56614e4b471015224a4d9ce26d0c1c241e45f7777590c1
private def q18 : Array ℕ := natRow 13 56 0x91a91ef9190e2491a91ef9190e24728e7b4de7d100903f3a78ddb55885dca4d084740f74bdc489ec25af55a58477380b9254ef7376ff0eb0244a73fd70044b
private def q19 : Array ℕ := natRow 13 56 0x9953eea257fc639953eea257fc6379d997d558fe1597eb408618a79c8d6c74c600504f7c44928b3cf4fd5cf1e1d76af4da5c34247a02013c2a43ddf618b8ef
private def q20 : Array ℕ := natRow 13 56 0xa0f0de44a6eaa2a0f0de44a6eaa28116d455da2b2a9f89668c6399e094ee64b48c2c8f83bd80859dc44b64305f30adde22636af57614f3c83030343fbf6dc9
private def q21 : Array ℕ := natRow 13 56 0xa87fede005d8e1a87fede005d8e1884630cf6b583fa719ac8bbe8c249c62749c2808cf8b288e790e93996b60fc8300c76a6a93e66b37e6543611991dc8bebf
private def q22 : Array ℕ := natRow 13 56 0xb0011d7474c720b0011d7474c7208f67ad420c8554ae9c1284297e68a3c8a47cd3e50f9285bc658f62e77283b9ce63b0b271aef7596ad8e03be69549b5d93f
private def q23 : Array ℕ := natRow 13 56 0xb7746d01f3b55fb7746d01f3b55f967b49adbdb269b6109875a470acab20f4568fc14f99d50a4b20323579989712d699fa78bc2840adcb6c41af28c386bd49
private def q24 : Array ℕ := natRow 13 56 0xbed9dc8882a39ebed9dc8882a39e9d8106127edf7ebd773e602f62f0b26b64295b9d8fa1167829c10183809f94505983427fbb792100bdf8476c0f35a54fa2
private def q25 : Array ℕ := natRow 13 56 0xc6281c036991d9c6281c036991d9a4708515121c60c4c6c5aaf6b613b99f0baefc4b07a841cd2700f93787919013c35cc986a5c8873aa0c34db826b68484cd
private def q26 : Array ℕ := natRow 13 56 0xcd716b7be88018cd716b7be88018ab5a216bc34975cc114b8771a857c0cd5b73b82747af671af791c8858e7c6d433646118d88f9597d934f546e06baeee208
private def q27 : Array ℕ := natRow 13 56 0xd4a2cae85f6e53d4a2cae85f6e53b22cc05fe68657d343f2c3c8fb7ac7e422eae8d4bfb6758fe661c039955188f8301f98945668b147761a5b1055b04f6404
private def q28 : Array ℕ := natRow 13 56 0xdbc58a4d865c8edbc58a4d865c8eb8f0bf4cb9c339da67f9f8d04e9dceec4a5ac98237bd7564cde1b7ed9c1804a5d9f91f9b153801c158e561a4049e5fe600
private def q29 : Array ℕ := natRow 13 56 0xe2d9a9ab5d4ac9e2d9a9ab5d4ac9bfa61e323d001be17d612687a1c0d5e5d1c35a2fafc46699ae11afa1a2cfe04c33d2a6a1c5674aeb3bb0682913852067fc
private def q30 : Array ℕ := natRow 13 56 0xe9df2901e43904e9df2901e43904c64cdd10703cfde884284ceef4e3dcd0b9249add27cb492e86f1a755a9791beb3dac2da866f68cc51e7b6e9f826490e9f8
private def q31 : Array ℕ := natRow 13 56 0xf0ca784b43273bf0ca784b43273bccda5e8af589acef70d0d212a8e5e3a1d837305bd7d212aa7cf0c76fb00a560eae75f3aef0845305f18575002033d790b5
private def q32 : Array ℕ := natRow 13 56 0xf7b25792fa1576f7b25792fa1576d3637d5a58c68ef659f7e9a9fc08ea6f1f89a1094fd8d79f4700bf23b695f19ee84f7ab57473860fd4507b58ef047812b1
private def q33 : Array ℕ := natRow 13 56 0xfe7f46cd2903adfe7f46cd2903add9d29ec5ae133dfd28405f9db00af121de8d0687ffdf82bb2dcfdf3dbd08cbb3291940bbdfa13d20a75a819b2cc48eb96e
private def q34 : Array ℕ := natRow 13 57 0x1053cd5ffa7f1e4829e6affd3f8f2380c980a54d7fb207ce519bc2c818f7c53d88bc06af730f3b86777fabb0db116fee78c198476ddd902f4c887ce0a7cf5602b
private def q35 : Array ℕ := natRow 13 57 0x10beb052a76e01b85f582953b700db9a0b061522b26e152d6268ea301cfe593c7cc1855f765569722f0fb8b27017f126ab331910fb928649adc8df1882dac06e8
private def q36 : Array ℕ := natRow 13 57 0x1127c6446cdce4e893e322366e7273b2dd15f100245e2252f5f0ea59df04d0d320cbd547798dbaebce33f8b3fe76132499b459d73517df4216e93fc94cce8d266
private def q37 : Array ℕ := natRow 13 57 0x1190b73620cbc858c85b9b1065e42bcba21b2295571a2f73c69ef1c1e30b45b2054153f77cc458cfbdc405b58bb49078cc25da9cdecae35c7829a00f26e0f7923
private def q38 : Array ℕ := natRow 13 57 0x11f7cf26e73aab88fbe793739d55c3e3f4aabeb2c90a3c599a0711eba5119d68995ba3df7fecba4164e845b7121aae7abaa71b5f1c4e3e54e149fec1efd5c44a1
private def q39 : Array ℕ := natRow 13 57 0x125de5172ca98eb92ef28b9654c75bfc06ba3a903afa491f2d5f12156717e4ff2565f3c7830d0baf040c85b89478ca78a9285c1f55d0974d4a6a5c72b8499101f
private def q40 : Array ℕ := natRow 13 57 0x12c2f906f11871e9617c83788c38f413d849962dacea55c480a6f23f291e1c75a96043af86254d189b30c5ba12cee47297a99cdd8b51ee45b38ab921803c5db9d
private def q41 : Array ℕ := natRow 13 57 0x13270af63487551993857b1a43aa8c2b6958d18b1eda624993deb268eb2443cc254a939789357e7e2a5505bb8d1cfc68862add99bcd2433e1cab14ce47ae2a71b
private def q42 : Array ℕ := natRow 13 57 0x13891fe478763809c48ff23c3b1c04427ef272f0cffe6e8f29ce4b546b2a4bba4fb9b4b78c365370e10d78bd0002b4c430bbde523a22cb148dab6ec3fdf05975a
private def q43 : Array ℕ := natRow 13 57 0x13eb27d2b6e51b39f593e95b728d9c598d816d0e41ee7ad2fce56b7e2d305270bb54049f8f3634ce4831b8be7228c8a61f3d1f0a57a1160cf6cbc866c45d262d8
private def q44 : Array ℕ := natRow 13 57 0x144b26bfefd3fe2a25935ff7e9ff14701d9acbb3f31286d5d2b3a469ad3638fed51325bf922659b8a6ea2bbfdcb67cd5c9ce1fbea8ef87e367cc2046799455317
private def q45 : Array ℕ := natRow 13 57 0x14aa17aca1c2e11a550bd650e1708c866a340899a43692b6e870fd552d3c0eace66246df950e0e9ecda29ec1430c2ee9745f2070de3cebb9d8cc77182e4484356
private def q46 : Array ℕ := natRow 13 57 0x1506e7984231c3ca8373cc2118e1e49c3257a707948e9e5400e3ef026b41c2b2a516393797e547118bef44c2a169811adaffe11f175a5e6e51accc0ed1b315856
private def q47 : Array ℕ := natRow 13 57 0x15629d8355a0a67ab14ec1aad0533cb1b3fb223584e6a9cdd94540afa94765185afa2b8f9ab3af7fe23beac3fb5ed11841a0a1cb1c76b722ca8d1feb7494a6d56
private def q48 : Array ℕ := natRow 13 57 0x15bd396ddc0f892ade9cb6ee07c494c6ef1e7a23753eb5247194f25ce74cf5de080e1de79d7947e9d08890c550ec1ee1a8416274ed91f5d7436d72ae16e938256
private def q49 : Array ℕ := natRow 13 57 0x1616bb57d57e6bdb0b5dabeabf35ecdbe3c1aed16596c057c9d3040a25527503ac52103fa036104f56d536c6a2116a770ee2231c8aac1a8bbc4dc456b8b0c9756
private def q50 : Array ℕ := natRow 13 57 0x166f234141ed4e8b3791a0a0f6a744f091e4c03f55eecb67e1ff75b76357e28947c60297a2ea08b07521dcc7eeceb3d87582e3c1f3c52540352e14e559eb5ac56
private def q51 : Array ℕ := natRow 13 57 0x16c5402987dc30fb62a014c3ee187d04b1122df5857ad62ebcdee0265f5d2bc68f4ec627a58c349d8302b5c932eb9d03983364630cae14d2b5ee636ee9cf4e617
private def q52 : Array ℕ := natRow 13 57 0x171a37113acb136b8d1b889d6589b51886bf76ebb506e0d0d7abea955b6262a3cda789b7a8253085f8e38eca727083e2bae3e501d995de6536aeb0d2792041fd8
private def q53 : Array ℕ := natRow 13 57 0x176ccaf7bb39f59bb6657bdd9cfacd2bc777192a23c6eb26b52a6dc6156773b8b7551e7faaab9ff9fe589acba8f50a5b99a4259c264d74d5bf4efc18f70e97e5a
private def q54 : Array ℕ := natRow 13 57 0x17be2cdda2a8d7cbdf166ed1546be53ebbae95289286f5565295d0f6cf6c71ad9772b347ad287f693bcda6ccdab18e70786466340f03d94647ef462d7463edcdc
private def q55 : Array ℕ := natRow 13 57 0x180e5cc2f117b9fc072e61788bdcfd516365eae70146ff5fafee142789715c826e00480faf9bced3b142b2ce07a610215724a6c993b90bb6d08f8f0ff12043b5e
private def q56 : Array ℕ := natRow 13 57 0x185d5aa7a6869c2c2ead53d3434e1563be9d1a6570070942cd333758437634373afddcd7b2058e395eb7becf2fd28f6e35e4e75cb46d0c27592fd6c06d43999e0
private def q57 : Array ℕ := natRow 13 57 0x18a9d18b17757e1c54e8c58bbabf0d757bde9eac1dfb12d52d27934abb7ae3e3b23042d7b45ba12a0bc0fdd04e6eae0cd0b4e7eb0cf0b575e9b01c2fd7f251d23
private def q58 : Array ℕ := natRow 13 57 0x18f50a6de964600c7a8536f4b2300586e99ffb32cbef1c3fcd080f3d337f7fb01f72a8d7b6a7c415c0ca3cd16812ca2f6b84e876e97320c47a30606142020a066
private def q59 : Array ℕ := natRow 13 57 0x193da44f6ad341bc9ed227b569a0dd97b36ba981b9172556af9643f16983f1f43629e00fb8df7a8c1567aed277c68573c264a8fdcdc51cf11290a2399a912486a
private def q60 : Array ℕ := natRow 13 57 0x1984f4304742236cc27a1823a111b5a82ab72e90a63f2e44520fd8a59f884f9842911747bb0ce0fd420520d382523e24194469821e15cf1daaf0e2c7f27b3f06e
private def q61 : Array ℕ := natRow 13 57 0x19c98d0fc73104dce4c687e398826db7f80d0267d29b36db3735a61b938c8233f7ad1fb7bd251af8ae36c5d4828d95c62c33ea014635fa284b3120e538d8bbd33
private def q62 : Array ℕ := natRow 13 57 0x1a0ccfee9c1fe64d0667f74e0ff325c76fe2ab7efef73f475c46139187909f6fa2192827bf32a4eec2686ad57d70eabc3f236a7dc254cf32eb715dac7e8b389f8
private def q63 : Array ℕ := natRow 13 57 0x1a4ebcccc60ec7bd275e66630763ddd6923829d62b534788c14121077b94a74b41d53097c1357edf7e9a0fd672fc3d065212eaf792724e3d8bb1991dc392b56bd
private def q64 : Array ℕ := natRow 13 57 0x1a8dd4a9847da8ed46ea54c23ed475e50317f33596e34f6fa8e6873f2d98823e89560a3fc3223c5a025fe7d75dbf2e0621122b6bfe5f282633d1d1fff6fe94843
private def q65 : Array ℕ := natRow 13 57 0x1aca0584ce6c89dd6502c2673644edf2be02055d41a756f9d33526389d9c2f29780bb51fc4f84d5e05b9f2d83d71bd97ac212bdae21b4aece3d2084118c5d5e8a
private def q66 : Array ℕ := natRow 13 57 0x1b04c85f615b6acd82642fb0adb566001d6be9c4ec6b5e563d6ce5320d9fc5345b515fffc6c2ee5c5113fdd9176c4a4d37302c46e9d5ffb393d23d1439d6174d1
private def q67 : Array ℕ := natRow 13 57 0x1b3c8c3873ca4b7d9e461c39e525be0cc0e013f4d6636552ea4c5ced3ba32bb6e50bdc17c87622e3bc023bd9e5f675647e4eecad395fe5584bb26f2e4935bafd9
private def q68 : Array ℕ := natRow 13 57 0x1b72d610c9392c2db96b08649c96161905d40ee4c05b6c20571434a869a67a9962f6582fca1d87653ef079daae989d87c56dad1094e850fd03929fce57d85eae1
private def q69 : Array ℕ := natRow 13 57 0x1ba608e792280c9dd30473c914064e2488d24c9ce987728b0682452555a998738695a57fcbacbf6f8172eadb6b6a63dcc89c2d6e083fd57fc352cd9d54be64aaa
private def q70 : Array ℕ := natRow 13 57 0x1bd612bcc596eccdeb095e62cb76662f455acadd51e77890b8956e63ffac84254f59c407cd233b023b898edc1c23c83f87da6dc56f6660e08af2f8893fdeccf34
private def q71 : Array ℕ := natRow 13 57 0x1c02e1905a85ccbe0170c82d42e65e3936ed8765f97b7e2f2d4c906467af3c8ebcb2b3c7ce806a1d253465dcc07cca8c03286e16a65be11f5a73208019309787f
private def q72 : Array ℕ := natRow 13 57 0x1c2e12632074acae170931903a565642c100102ea10f8399e1e9d264cfb1db181d1ba387cfd0a93196df3cdd5e5dc99c7e766e64a14fc35e29f346d8f1b3621ca
private def q73 : Array ℕ := natRow 13 57 0x1c543b3360638c1e2a1d99b031c60e4b10a74347c70b8863dbe5e5e8b3b429f0d21e35b7d0f9bf5c1fb279dde936075c71e3eea917e2fd59093368b5a74ff1497
private def q74 : Array ℕ := natRow 13 57 0x1c78ae02c5526b8e3c570162a935c652f2ce3fa0ed078cf715c6996c97b65d697970c7e7d215257fd085b6de6d3641b065516eea22748153e87388dc5c1180764
private def q75 : Array ℕ := natRow 13 57 0x1c97e8cf8c414a7e4bf467c620a53e598e89e04a916b90e395031e73f7b83e3173dcfc87d307e2b8d88159dedd6dba53d0de6f2148a52d0ad773a456edd4d43b3
private def q76 : Array ℕ := natRow 13 57 0x1cb5559b6c30296e5aaacdb61814b65fb6c5473435cf94965422c37b57ba02195fd93127d3ec2feaa87cfcdf466d2f5b3c6b6f54d2d40ac1c673be037eb128002
private def q77 : Array ℕ := natRow 13 57 0x1cb98b5aa39f051e5cc5ad51cf828e5fc287f0c90fd79523f6a28a595dba37d52da4059fd40ddb4a02ff36df51a7cad134c52f597a961fbf1bd3c206307379a1e
def row1 (v : ℕ) : Entry := (#[⟨q0,1⟩,⟨q1,1⟩,⟨q2,1⟩,⟨q3,1⟩,⟨q4,1⟩,⟨q5,1⟩,⟨q6,1⟩,⟨q7,1⟩,⟨q8,1⟩,⟨q9,1⟩,⟨q10,1⟩,⟨q11,1⟩,⟨q12,1⟩,⟨q13,1⟩,⟨q14,1⟩,⟨q15,1⟩,⟨q16,1⟩,⟨q17,1⟩,⟨q18,1⟩,⟨q19,1⟩,⟨q20,1⟩,⟨q21,1⟩,⟨q22,1⟩,⟨q23,1⟩,⟨q24,1⟩,⟨q25,1⟩,⟨q26,1⟩,⟨q27,1⟩,⟨q28,1⟩,⟨q29,1⟩,⟨q30,1⟩,⟨q31,1⟩,⟨q32,1⟩,⟨q33,1⟩,⟨q34,1⟩,⟨q35,1⟩,⟨q36,1⟩,⟨q37,1⟩,⟨q38,1⟩,⟨q39,1⟩,⟨q40,1⟩,⟨q41,1⟩,⟨q42,1⟩,⟨q43,1⟩,⟨q44,1⟩,⟨q45,1⟩,⟨q46,1⟩,⟨q47,1⟩,⟨q48,1⟩,⟨q49,1⟩,⟨q50,1⟩,⟨q51,1⟩,⟨q52,1⟩,⟨q53,1⟩,⟨q54,1⟩,⟨q55,1⟩,⟨q56,1⟩,⟨q57,1⟩,⟨q58,1⟩,⟨q59,1⟩,⟨q60,1⟩,⟨q61,1⟩,⟨q62,1⟩,⟨q63,1⟩,⟨q64,1⟩,⟨q65,1⟩,⟨q66,1⟩,⟨q67,1⟩,⟨q68,1⟩,⟨q69,1⟩,⟨q70,1⟩,⟨q71,1⟩,⟨q72,1⟩,⟨q73,1⟩,⟨q74,1⟩,⟨q75,1⟩,⟨q76,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩,⟨q77,1⟩][v]?).getD zero
private def ok (v : ℕ) : Bool := if 182≤v then true else
  check 1 v (FinalLedgerData6815.row 1 v) (thresholds (SingletonData6815.row 1 v)) (row1 v) (row0 v) (if v=0 then zero else row1 (v-1))
private theorem g0 : allN (fun j => ok (16*0+j)) 16=true := by decide +kernel
private theorem g1 : allN (fun j => ok (16*1+j)) 16=true := by decide +kernel
private theorem g2 : allN (fun j => ok (16*2+j)) 16=true := by decide +kernel
private theorem g3 : allN (fun j => ok (16*3+j)) 16=true := by decide +kernel
private theorem g4 : allN (fun j => ok (16*4+j)) 16=true := by decide +kernel
private theorem g5 : allN (fun j => ok (16*5+j)) 16=true := by decide +kernel
private theorem g6 : allN (fun j => ok (16*6+j)) 16=true := by decide +kernel
private theorem g7 : allN (fun j => ok (16*7+j)) 16=true := by decide +kernel
private theorem g8 : allN (fun j => ok (16*8+j)) 16=true := by decide +kernel
private theorem g9 : allN (fun j => ok (16*9+j)) 16=true := by decide +kernel
private theorem g10 : allN (fun j => ok (16*10+j)) 16=true := by decide +kernel
private theorem g11 : allN (fun j => ok (16*11+j)) 16=true := by decide +kernel
theorem checked1 (v : ℕ) (hv : v≤181) :
    check 1 v (FinalLedgerData6815.row 1 v) (thresholds (SingletonData6815.row 1 v)) (row1 v) (row0 v) (if v=0 then zero else row1 (v-1))=true := by
  have h : ok v=true := by
    rcases (show (0≤v ∧ v<16) ∨ (16≤v ∧ v<32) ∨ (32≤v ∧ v<48) ∨ (48≤v ∧ v<64) ∨ (64≤v ∧ v<80) ∨ (80≤v ∧ v<96) ∨ (96≤v ∧ v<112) ∨ (112≤v ∧ v<128) ∨ (128≤v ∧ v<144) ∨ (144≤v ∧ v<160) ∨ (160≤v ∧ v<176) ∨ (176≤v ∧ v<192) by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
    · exact CompactAllN6815.allN_block ok 0 g0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 1 g1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 2 g2 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 3 g3 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 4 g4 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 5 g5 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 6 g6 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 7 g7 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 8 g8 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 9 g9 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 10 g10 v (by omega) (by omega)
    · exact CompactAllN6815.allN_block ok 11 g11 v (by omega) (by omega)
  simpa only [ok,if_neg (show ¬182≤v by omega)] using h
end ProximityPrize.SubmissionLower.FinalPrefixRows6815
