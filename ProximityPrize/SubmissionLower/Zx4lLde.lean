import ProximityPrize.SubmissionLower.Z9Zvicc
import ProximityPrize.SubmissionLower.ZyrUiId
set_option Elab.async false
section
set_option autoImplicit true
namespace qtqUEwc
open P6_7_3 (IntroIndex)
open qUrGXob (Trial graphRate)
def digit (w p i:ℕ) :ℕ:=(p >>> (w*i)) % 2^w
def dN (o:IntroIndex) (i:Trial) :ℕ :=
  digit 33 (([0x9c43c9cd8af215ba54c90544286509b6c3286bf3d04dcddb640c13244c0966a756080440fb00ab5546c044006d60196a419,
    0xc45b8595831df0ab5d3cf7230bddc31594772d6c507310273c0324017c020cd356015f87ef00327936001a92528009ee677,
    0xc61c71ad4d21c3541d247e328bcb624514703efbf05ee2459c02e84a420238e1f30152a5dd00267f0c40137d97400797c20,
    0xab4fa7d143f0f5bc99dae2f78a6f143483ec95c5e0041c3f78029b17b601e13b7501248f28001c1ec9400dbf5640058ed03,
    0x754033cce0fae2ae1a4321e008afcdb351aca4ff0043f81bc0318a848025abeb4017591db001e0237800e0188e005f2620,
    0xcd3dfe7f57104fa620eb0b798d51916a75030915e04d8ba76002cb8cb201fce9170133ad78001ef7a9c00f4f2ac0061de21,
    0xc220fa58d3a5883ee3b1aee20e69c0a8356bcb20f0042c734c02eaa3aa02335e93015c3707001cbf71400d84a3a005b1cc5,
    0xdf2f87e1e280695269ef68fe10f5ea6ed661a65bd05cb3b2c4035a0d76026710bd017504b5002499f4c011fa12e0073b6e3,
    0xc88bf8fc91634f95eb6479d5f1821f22a695ae9a8004b6467003613c5a0297c7d3019cb7c200201babc00ed3c880065dcc1,
    0x46a0e8e018a5d6a0095d4bde03c81273016c1d3d001b04ec401216ad000d866d00085541f000b5c208005626ca0023fc9e,
    0x59df24401f49c3800be3e67204cd0fa301ce45fb00220f8bc016fd19c0113e4ea00aa2d3b000e57650006c70f6002d7082,
    0x918542f8406cb8d41d3021480bccfcb9047067fd005b81d34037bfdee02812581018547bd0025da05c012893b20077af49,
    0x8d5f85783e426aac19a93f460a614ea903e7a9400053e7420030d2fd802264aec014b6c330022653b801121500006ca805,
    0x88162e503b8ee4c818d935240a0bc6aa03c76e08004e6ba2002f843380221a914014b06ee00205c72000fe86f000664f06] :List ℕ).get o) i.val
def dD (o:IntroIndex) (i:Trial) :ℕ :=
  digit 5 (([0xc1318c408420820,
    0xc0318c400000000,
    0xc6318c400000000,
    0xc6318c000000000,
    0x6300c000000000,
    0xc6318c400000000,
    0xc6318c000000000,
    0xc6318c400000000,
    0xc1318c000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0] :List ℕ).get o) i.val
def d (o:IntroIndex) (i:Trial) :ℚ :=
  ((dN o i:ℕ) :ℚ)/((dD o i+1 :ℕ) :ℚ)
def bN (o:IntroIndex) (i:Trial) :ℕ :=
  digit 68 (([0x148ed211f7aa0b50007d90bf80a72074000cfa1dd207bf0c1e0005b5339de229ea8010618fdd44999ca9dd6254fed532589ea0682e461d91811aa50682e461d91811aa5000671ccd9d3efad927115a4b169069fde08ae85d7cc20178dc0d05c8c3b2302354a,
    0x2c9fe48b7851df80004670efd823834c0116c1b087f4a104000a30bd42a15bf57802ae623a49e8f8b9ddd6254fed532589ea0682e461d91811aa50682e461d91811aa50009e637cd66e1bab001828694d59646e10682e461d91811aa5045742ebe6100bc6e,
    0xc90b8be463bd00021b91ad9ad8d428005d8443a50a6424000a4f1351eb2bd43800171f81c8fea80e0dd6254fed532589ea0d05c8c3b2302354a0d05c8c3b2302354a00000053007a44fc90d05c8c3b2302354a0682e461d91811aa50682e461d91811aa5,
    0x8d9e29fe8ae1ef7000548a787e202cf20045cede25f0bd2370004e9106c6e23e290368c58ddae83740f0682e461d91811aa50d05c8c3b2302354a003a7cc90c1bcab9a0682e461d91811aa500af765b2453602ce022ba175f30805e370d05c8c3b2302354a,
    0xecfde93e0e78006dc93fcad6746d00002f3413b42c678f0002d3a317635f6c0001dc714f667a0ca4045742ebe6100bc6e022ba175f30805e370030a77e05b2096580060f84428461e4cb0682e461d91811aa5045742ebe6100bc6e001d3e64860de55cd,
    0xa5683b88ae0118002dc7d54bc9dd1bf00e11ecb74589d5370083b88b9c8547344022bacf1d9f661ac46eb12a7f6a992c4f50d05c8c3b2302354a0d05c8c3b2302354a002ec5f0cf804070800c41ade55c698aaa0682e461d91811aa50d05c8c3b2302354a,
    0x2d720f914b9dbc801276fce9434030100004572d2fa83ffe8023cf84091902c4c000603869abc6955090d05c8c3b2302354a0090f277d0185a94601726ba3f75aae97a0000004eba03096cc01726ba3f75aae97a045742ebe6100bc6e0d05c8c3b2302354a,
    0xaed67e623992076000ecbaad0d34aa58009309f0769866fd5001c3dd7549cb89880047783d0ec00f2f549cb71aa4710c834e0090f277d0185a9460118e60d9f7b9b04800019ef4515b54d000d05c8c3b2302354a0d05c8c3b2302354a0d05c8c3b2302354a,
    0x6278c6fd0358380037165fa12a6420001146062f4be0543800011ec15a574565c00435de0fb4b9cbcb0682e461d91811aa50d05c8c3b2302354a00309985c598e8906001ac805bcd17994f0d05c8c3b2302354a0682e461d91811aa50d05c8c3b2302354a,
    0xc633826077abc00000c568fc1a04e84001a8de2628fc4bec0007eec7c8e1414a0001977d95b22aa0700d05c8c3b2302354a00b935d1fbad574bd0682e461d91811aa50682e461d91811aa50682e461d91811aa50d05c8c3b2302354a0682e461d91811aa5,
    0x19b38e47927dc8000313c2d119588930001230a769edd74c00051231dc0952a4800207099a6f4b3d700d05c8c3b2302354a022ba175f30805e370057bb2d9229b01670682e461d91811aa50682e461d91811aa50090f277d0185a9460682e461d91811aa5,
    0x6d325fd81a9ad60000735181e7e5d180004fd5f082bff8b10002f2f98cc225df80003115c36c88d0c0003a7cc90c1bcab9a0d05c8c3b2302354a005685f6df32d58e800047c70dd6d9ddc40d05c8c3b2302354a045742ebe6100bc6e0d05c8c3b2302354a,
    0x25f541646e1be800004acbb12d59ca8000000ea844ac777000062d0b8e4c81782000315ba75b0bda330682e461d91811aa5022ba175f30805e370682e461d91811aa500185d4787acac5f30057bb2d9229b01670682e461d91811aa50d05c8c3b2302354a,
    0xf738c1ca2551000009addfa5d305840000025d1cf71cd9d0009d3c42c7c07ec700034a7a94cd0eec80682e461d91811aa50048793be80c2d4a30682e461d91811aa500186b40b1feea9d30682e461d91811aa50682e461d91811aa50682e461d91811aa5] :List ℕ).get o) i.val
def bD (o:IntroIndex) (i:Trial) :ℕ :=
  digit 56 (([0x19553fc2e6d02c051e3af19912360525a3e056b56600187bed117e1a029769608f6fa9c35496ff7fd89805be7a6803474b05bbdf9e20a573000a8dbdba6fe3227e3077ff4ada07a962c5b7b9be0b7a019a6c3f78,
    0x505c2a3df446c00567a524617740cc64c71681b9a052252101678420ce654bca0f109c30c75cb6de13a05bd12c26b10c305bb3736e16827000c1a7db017e3001555b419180e05bff03248296403d5d55632ca70,
    0x16f3810d388a0288ce7e81a7f20442307386d0c205227b768e279a006e167defd868c333866ecdcf020b7b0cb9f86f900b7519449dfb460000005e96a1150b81a6122b6ec005c0cb86992f7d05c150debec976,
    0xca0084dcc3f5500516ca050bdde028ff7085a0f3e001f5ec37713280cec6da8b49aaa05bf2cb61af1730b7c379eaa11fe0033811f6de97405ba4dc5b003be009b19a7e9cd0e01eb29ce4a34a50b839ddd541676,
    0x18215cbeb2c0871d1042a333e002ca0f6b8a08c001d1f26d0fc1000b7101b9ed6ba03d4b1b8bfd56801e9b83e33b03e002c6ce5732e52008513e4d5cfc705c1567c2eb6f303d64e459f16400019dac9604e2e,
    0x140d08b99cd160434aeec4c32a20cbbefb671a592051f0c84051e640ce02d80a084bc61aa8b949867fa0b7b7c01014e380b76e9ab1eab32002c6b6ab08e2c00ad53b8cfeab205c14d0a5cc1270b83589f4e3a90,
    0x506634c1063aa1945b8ca5ef08c004844f2d36e7a198eeaced37d380292505288d1c30b7e3a0e6c57e6007fc881743e5a0145eb1b4e37ae0000005e91d88001476ce43c395403d65858aa78560b838ceec8c0fc,
    0x18f707921b8e7401ac86b2aa24600ca28bbcdfa6f401b24816b7360c029026803356a94112954240930a007fb5c01d92b8010a84b45f2202000237cdfcb1b60b81e0c39c18e60b81f4d36f91b20b82ce6ca48016,
    0xb782f3525714050c16fdfc2300193ce279cc0ee0001213f34b4a08028fb149e09f9005be979eddde700b793872d58e34003546e3336530002c52c7dfc52c0b826bf10852fa05c15bf81ab9ec0b8339b07ffa70,
    0x82ff66dafc8400044189b996e400584e0050779a0011b4051bf05a002146a2f8f06a0b830990e7e54000a3a9a94f3d8a05bfe15f01d87e05bf1eca98240305c2774d8787a90b8500e8d168dc05c29be6deb093,
    0x1a07bb703af6001a453825e0600005de026fa8960011a7c5f42de600426abbbff5400b822f75b0f17a01eaca643b7df3004d6b871b9ee105be01744e7cd705c24920a449e4008033f081977805c2774d8787a9,
    0xff67bb628300000d8503c3cf080080f7e587ed260033fb093d87d20020bebba6ee6a003390c605103c0b78d0da9d78d20058d0c998819c0006a6d78694480b81ba09bc883203d5f0ba562d920b82afae0d8f08,
    0x5541b83aef2600084c69f8198e000012c23b75740056f7bb633ae8001a457059c77005be13ce77b75201e9bfa5162da205bad49c538568001aa38274816f004d87b6840b4305c114a3c5cd060b8305144faabc,
    0x200787e6411400101ba88b89d400002e208029fb008291b4149a41001a49f9fcc4ea05be68b8b50992003fe31b2e4ab605bae68bae1324001aa390b68f6605c1320d57527205c13a7f046bfa05c19b1dd220af] :List ℕ).get o) i.val
def b (o:IntroIndex) (i:Trial) :ℚ :=
  ((bN o i:ℕ) :ℚ)/((bD o i+1 :ℕ) :ℚ)
def residualN (o:IntroIndex) (i:Fin 4) :ℕ :=
  digit 95 (([0x122c3b99781a69cb7c00000007471191693259c538000000052e963cedc0852ec80000000000006720b8ecedc,
    0x94be111b373dd38a9380000000000000ed64a6003e62bba571e661b0c0d5020c7e00000000001e501da9d55695,
    0x94be111b373dd38a9380000000000000ef83636ea780a022bea9a4b6d3ac3d20fc00000000001f161fbc25d775,
    0x22ff8b8deee15ef36e0000000000000cf1ccd632d879e0b3fc89fba148e912f9a000000000013440188304875,
    0x2eaa0f67e92c7e99e8000000000000008dc11e9a4c00013edd76f5c9af16a1ee200000000001882ed7e320955,
    0x4a5f088d9b9ee9c549c0000000000000f822732e8a890ef5d303917386821603840000000000223b53cb20fff5,
    0x8bfe2e37bb857bcdb80000000000000eab2dea9fee25b06d38abaaa44fe4a009600000000001d5476ad3cc555,
    0x3194b05e67bf468386800000000000010dd3f6c720673efdbb3ef4ebe917081abe00000000002a256b2a2f6195,
    0x45ff171bddc2bde6dc0000000000000f275398544c51024675f1e288f8284beba00000000002029257c7e5655,
    0x3881ea4234e93f880000000000000005563898ad000412e53621e7e40ac9e33800000000000003e19cb79ab3,
    0x47f9d4ea6eef05080000000000000006ca746536000526537318064ed0f5681000000000000004ed7c999be3,
    0x274bd71422ac34b7800000000000000afee9c76d400345ba0f9b912fd4d954e600000000002bfe8e0ccce615,
    0x45ff171bddc2bde6dc00000000000000aaeafbdc940054e5c0674c8be8b412cca00000000002922d37cc8f015,
    0x45ff171bddc2bde6dc00000000000000a486d0fdb8001eb3b0c1cbe9e6e141d140000000000257e21f8b06375] :List ℕ).get o) i.val
def residualD (o:IntroIndex) (i:Fin 4) :ℕ :=
  digit 56 (([0x14bb4b047b7d4000000279cae4e00000018b686cc00000000000004,
    0xc30c75cb6de13a000000000000187d900200cdaea4000000000001f3,
    0xc333866ecdcf0200000000000018023dc79a4a8592000000000001f3,
    0x2df965b0d78b9000000000000181f9014c27e9e56000000000001f3,
    0x3d4b1b8bfd5680000000000000000004d378f2f08000000000001f3,
    0x61aa8b949867fa000000000000181f545da205073e000000000001f3,
    0xb7e3a0e6c57e6000000000000187d9fb26d99bbb2000000000001f3,
    0x4112954240930a000000000000187cd325da89c848000000000001f3,
    0x5be979eddde700000000000001811ebc9c30a810c000000000001f3,
    0x2146a2f8f06a00000000000000001a331492328000000000000000,
    0x426abbbff54000000000000000001a07bb703af600000000000000,
    0x3390c605103c00000000000000000a37596a5728000000000001f3,
    0x5be13ce77b7520000000000000000110d24d8963a000000000001f3,
    0x5be68b8b5099200000000000000000667e7fad9d0000000000001f3] :List ℕ).get o) i.val
def residual (o:IntroIndex) (i:Fin 4) :ℚ :=
  ((residualN o i:ℕ) :ℚ)/((residualD o i+1 :ℕ) :ℚ)
def factorJumpN (o:IntroIndex) (i:Fin 3) :ℕ :=
  digit 207 (([0x58d555eae5b331a416f51d1f708584000000000000000000000000000000009fd7ce65354cefc65930000000000000000000000000000000013c284ddf15152bf5b10,
    0x16552c2920b2548859cd03280b2367830a2151154c08f966780000000000000000000032cf2758ab411fd4ac78940222ba033000000000000000000000000000001768ce4495619956e718449,
    0x1b9b6c228df94dd7acac3569d1da2cc74282468d3350ac25ff2ac0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x26170944166c3a2965c25f353ffba91155bbf4410cd2611c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x2ad8c8bb974e54a5bfdb665e799acc3d77b4800000000000000000000000000000000000013c765444bbb7a1,
    0x83a9955d6bf013d8115c8f06c69d3cdaaaf3cf2183c7600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x42f27446ebfdf18bbcd056c780fef6a93887b619115e7e0a3a0000000000000000db58e1dcbd9ea00f50921a4cff9974e7a115800000000000000000000000000000000000011743eacf66003b,
    0x1e4fa6a11492aaf7fb3b8c3b16715874ec7b8e09781a6c6e432c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x9b9885b94057bf13406bd4b16e7261ffa157020f91c6a7c00000000000000001f5b9055a460686e4e04aa2280e954b49f800000000000000000000000000000000000000b91ac112ea5100,
    0x0,
    0x0] :List ℕ).get o) i.val
def factorJumpD (o:IntroIndex) (i:Fin 3) :ℕ :=
  digit 164 (([0x2b38e0b0703d26a21b800000000000000000000000000000000018b686cc000000000000000000000000000000000279cae4e,
    0x2f689120c5f5241c58ec952251a0f7927244fc000000000000000000000005617a84f9b06d9e40200000000000000000000000000000004d5e04724b,
    0x88567e5489db0055073ad9aefb43d1a90a8b2b3ae0000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x83bcdb79e5cb43e95c251a384cb5eec7236c0000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x2ba82ff00920f2c79b292f79000000000000000000000000000000000000001f3,
    0x7e78568525fa2aceb5c563fb334e23a869e0000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x1319b469d1ad079cb5eb820c948e0a2cfe373b3a000000000000000002b6685b6b09b016230ea628100000000000000000000000000000000000000063,
    0xaa3d4cfa3c895f8cff71ffa052ba7ccdeb45d5760000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x11406b9b288a9f13b27bf56c88bd7f74f5e680000000000000000000b0e7ac73649b00b4f8247e0000000000000000000000000000000000000007c,
    0x0,
    0x0] :List ℕ).get o) i.val
def factorJump (o:IntroIndex) (i:Fin 3) :ℚ :=
  ((factorJumpN o i:ℕ) :ℚ)/((factorJumpD o i+1 :ℕ) :ℚ)
def a (o:IntroIndex) (t:Trial) :ℚ:=max (d o t) (graphRate 55)
end qtqUEwc
end
section
set_option autoImplicit true
namespace qJeTDGe
noncomputable section

open qehP9ee

open scoped BigOperators
end
end qJeTDGe
end
section
set_option autoImplicit true
namespace qJeTDGe
noncomputable section
open Finset qehP9ee

open scoped BigOperators
private theorem tail_swap {n:ℕ} (w x :Fin n→ℚ) :
    (∑ j,(∑ i,if i≤j then w i else 0)*x j) =
      ∑ i,w i*(∑ j,if i≤j then x j else 0) := by
  simp only [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  split <;> simp_all
end
end qJeTDGe
end
section
set_option autoImplicit true
namespace qtqUEwc
open P6_7_3 (IntroIndex introCap lineFee)
open qUrGXob
open qehP9ee (asShape kK mixedCols)
open TD (GM FP XM)
open qJeTDGe (bbD)
open scoped BigOperators
def stageDual (s :bAL) :GM :=
  if s=10 then ![0x6d9abd44445f3/125,0,0,0]
  else if s=11 then ![0x5c7620ab2b933/100,0,0,0]
  else 0
def freeDual (o:IntroIndex) :GM :=
  if o=0 then ![0xbd57b98b8bff5/250,0xaae506b9f98/25,0xed04b4a9275/200,0] else 0
def bR (bw:Fin 3) (n:ℕ) :GM :=
  if h:n<12 then SS bw ⟨n,h⟩ else 0
def historyAt (n:ℕ) :GM :=
  if h:n<12 then bAW (Fin.succ ⟨n,h⟩) else 0
def cutBook (bw:Fin 3) :ℚ:=XM 12 (bR bw) historyAt
def stageBook :ℚ := ∑ s :bAL,FP (stageDual s) (bAW s)
def freeBook :ℚ := ∑ o:IntroIndex,FP (freeDual o) (preMoving o)
def factorBook :ℚ := ∑ i:IntroIndex,∑ j:Fin 3,factorJump i j*(introCap i.val j:ℚ)
def unit (o:IntroIndex) (j:Fin 3) :ℚ :=
  ∑ k :Fin 4,residual o k*(mixedCols (originShape o) k j:ℚ)
def envelopePrice (o:IntroIndex) (s :bAL) (k :Fin 4) :ℚ :=
  bbD stageDual s k+(if moveStart≤ s then freeDual o k else 0)+residual o k
def absorbs :Prop :=
  ∀ v :Fin 3→ℕ,(∀ j,v j≤ introCap lastOrigin.val j) →
    v 1≤v 0→0<v 1→0<v 2 →
    (lineFee (v 0) (v 1) (v 2) :ℚ)+FP (residual lastOrigin) (kK v (asShape v)) ≤
      ∑ j,unit lastOrigin j*(v j:ℚ)
end qtqUEwc
end
section
set_option autoImplicit true
namespace qtqUEwc
noncomputable section
open Finset qUrGXob
open TD (FP running XM)
open scoped Classical BigOperators
open qJeTDGe (bbD c44)
private def cutJump (bw:Fin 3) (t:Trial) (k :Fin 4) :ℚ :=
    running (bR bw) (t.val+1) k - running (bR bw) t.val k
private theorem cutJump_nonneg (bw:Fin 3) (t:Trial) (k :Fin 4) :
    0≤ cutJump bw t k :=sub_nonneg.mpr (le_max_left _ _)
private theorem cut_prefix (bw:Fin 3) (t:Trial) (k :Fin 4) :
    SS bw t k≤bbD (cutJump bw) t k := by
  have h:=Fin.sum_Iic_sub t (fun i=>running (bR bw) i.val k)
  change (∑ i∈Iic t,cutJump bw i k)=running (bR bw) (t.val+1) k - 0 at h
  have hf : (univ.filter fun i:Trial=>i≤t)=Iic t:= by ext i; simp
  rw [bbD,← sum_filter,hf,h,sub_zero]
  change SS bw t k≤ max _ (bR bw t.val k)
  simpa only [bR,dite_eq_left t.isLt] using
    (le_max_right (running (bR bw) t.val k) (SS bw t k))
theorem cut_bill (B:aAU) (bw:Fin 3) :
    (∑ f∈B.factors,∑ t:Trial,FP (SS bw t) (B.stops f t.succ))≤ cutBook bw:= by
  have htail (t:Trial) (k :Fin 4) :
      (∑ f∈B.factors,∑ j:Trial,if t≤j then B.stops f j.succ k else 0) ≤
        bAW t.succ k := by
    have hz : ¬ t.succ≤(0:bAL) := by
      change ¬ t.val+1≤0
      omega
    have hf (f :cu.Jet) :
        (∑ j:bAL,if t.succ≤j then B.stops f j k else 0) =
          ∑ j:Trial,if t≤j then B.stops f j.succ k else 0:= by
      rw [Fin.sum_univ_succ]
      simp only [ite_eq_right hz,zero_add,Fin.succ_le_succ_iff]
    simpa only [hf] using B.V8 t.succ k
  calc
    _ ≤ ∑ f∈B.factors,∑ t:Trial,∑ k,bbD (cutJump bw) t k*B.stops f t.succ k :=
      sum_le_sum fun f hf=>sum_le_sum fun t _ =>
        TD.dYl (B.nonneg f hf t.succ) (cut_prefix bw t)
    _ ≤ ∑ t:Trial,FP (cutJump bw t) (bAW t.succ) :=
      c44 B.factors _ _ _ (cutJump_nonneg bw) htail
    _=cutBook bw:= by
      rw [cutBook,XM,sum_fin_eq_sum_range]
      refine sum_congr rfl fun i hi => ?_
      simp only [dite_eq_left (mem_range.mp hi),historyAt]
      rfl
end
end qtqUEwc
end
section
set_option autoImplicit true
set_option maxHeartbeats 800000
namespace qtqUEwc
noncomputable section
open Finset qUrGXob
open P6_7_3 (IntroIndex introCap wD)
open qehP9ee (asShape kK mixedCols)
open qJeTDGe (bbD c44)
open cu (Jet Shape)
open TD (FP a3x dYl)
open scoped Classical BigOperators
private theorem stage_nonneg (i:bAL) (k :Fin 4) :0≤ stageDual i k := by
  unfold stageDual
  split
  · fin_cases k <;> (simp <;> positivity)
  split
  · fin_cases k <;> (simp <;> positivity)
  · exact le_rfl
private theorem free_nonneg (o:IntroIndex) (k :Fin 4) :0≤freeDual o k := by
  unfold freeDual
  split
  · fin_cases k <;> (simp <;> positivity)
  · exact le_rfl
private theorem stage_bound (B:aAU) :
    (∑ f∈B.factors,∑ s :bAL,FP (bbD stageDual s) (B.stops f s))≤ stageBook :=
  c44 B.factors stageDual B.stops bAW stage_nonneg B.V8
private theorem free_bound (B:aAU) :
    (∑ f∈B.factors,∑ s :bAL,FP
      (fun k=>if moveStart≤ s then freeDual (B.origin f) k else 0) (B.stops f s))≤freeBook := by
  unfold freeBook
  rw [← sum_fiberwise B.factors B.origin]
  apply sum_le_sum
  intro o _
  calc
    _ = ∑ f∈B.factors.filter (fun f=>B.origin f=o),∑ s :bAL,∑ k :Fin 4,
          freeDual o k*(if moveStart≤ s then B.stops f s k else 0) := by
      apply sum_congr rfl
      intro f hf
      have ho:=(mem_filter.mp hf).2
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro k _
      by_cases h:moveStart≤ s <;> simp [h,ho]
    _=FP (freeDual o) (fun k => ∑ f∈B.factors.filter (fun f=>B.origin f=o),
          ∑ s :bAL,if moveStart≤ s then B.stops f s k else 0) := by
      simp only [FP,mul_sum]
      rw [sum_comm (s :=(univ :Finset (Fin 4)))]
      exact sum_congr rfl fun f _=>sum_comm
    _≤_:=a3x (free_nonneg o) (B.prefree o)
theorem dot_mixed (w:TD.GM) (v :Fin 3→ℕ) (s :Shape) :
    FP w (kK v s) =
      ∑ j:Fin 3,(∑ k :Fin 4,w k*(mixedCols s k j:ℚ))*(v j:ℚ) := by
  simp only [FP,kK,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring
private theorem pay_factor (B:aAU) (f :Jet) (hf :f∈B.factors) (hline :absorbs) :
    lineCharge f (B.line f)+(∑ s :bAL,FP (residual (B.origin f)) (B.stops f s)) ≤
      ∑ j:Fin 3,unit (B.origin f) j*(wD f j:ℚ) := by
  have hh: (∑ s :bAL,FP (residual (B.origin f)) (B.stops f s)) ≤
      FP (residual (B.origin f))
        (kK (wD f) (if B.line f then asShape (wD f) else originShape (B.origin f))) := by
    simp only [FP]
    rw [sum_comm]
    simp only [← mul_sum]
    exact a3x (fun k=>div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (B.initial f hf)
  refine (add_le_add le_rfl hh).trans ?_
  cases h:B.line f with
  | false =>
    simpa only [h,lineCharge,Bool.false_eq_true,ite_false,Nat.cast_zero,zero_add,unit]
      using (dot_mixed (residual (B.origin f)) (wD f) (originShape (B.origin f))).le
  | true =>
    obtain ⟨ho,hj,hu⟩:=B.line_ok f hf h
    have hsp (j:Fin 3) :wD f j≤ introCap lastOrigin.val j:= by
      have hmem:f∈B.factors.filter (fun f=>lastOrigin.val≤(B.origin f).val) :=
        mem_filter.mpr ⟨hf,by rw [ho]⟩
      exact (single_le_sum (fun g _=>Nat.zero_le (wD g j)) hmem).trans (B.nested lastOrigin j)
    simpa only [h,ho,lineCharge,ite_true] using hline (wD f) hsp (B.spend_order f hf) hj hu
private theorem aNI (B:aAU) (hline :absorbs)
    (hunit : ∀ o j,unit o j≤bbD factorJump o j) :
    (∑ f∈B.factors,(lineCharge f (B.line f) +
      ∑ s :bAL,FP (residual (B.origin f)) (B.stops f s)))≤factorBook := by
  calc
    _ ≤ ∑ f∈B.factors,∑ j:Fin 3,bbD factorJump (B.origin f) j*(wD f j:ℚ) :=
      sum_le_sum fun f hf=>(pay_factor B f hf hline).trans
        (sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (hunit _ j) (Nat.cast_nonneg _))
    _ = ∑ j:Fin 3,∑ i:IntroIndex,∑ f∈B.factors,
        (if i≤B.origin f then factorJump i j else 0)*(wD f j:ℚ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [bbD,sum_mul]
      exact sum_comm
    _ = ∑ i:IntroIndex,∑ j:Fin 3,factorJump i j *
        (∑ f∈B.factors.filter (fun f=>i.val≤(B.origin f).val),(wD f j:ℚ)) := by
      rw [sum_comm]
      simp only [sum_filter,mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro f _
      have hi: (i≤B.origin f)=(i.val≤(B.origin f).val) :=rfl
      by_cases h:i≤B.origin f <;> simp [← hi,h]
    _≤_:= by
      refine sum_le_sum fun i _=>sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      simpa only [Nat.cast_sum] using (Nat.cast_le (α:=ℚ)).mpr (B.nested i j)
theorem dual_bound (B:aAU) (hline :absorbs)
    (hunit : ∀ o j,unit o j≤bbD factorJump o j)
    (hprice : ∀ o s k,stopPrice a b o s k≤envelopePrice o s k) :
    (∑ f∈B.factors,(lineCharge f (B.line f) +
      ∑ s :bAL,FP (stopPrice a b (B.origin f) s) (B.stops f s))) ≤
      stageBook+freeBook+factorBook := by
  calc
    _ ≤ ∑ f∈B.factors,(lineCharge f (B.line f) +
        ∑ s :bAL,FP (envelopePrice (B.origin f) s) (B.stops f s)) :=
      sum_le_sum fun f hf=>add_le_add le_rfl
        (sum_le_sum fun s _=>dYl (B.nonneg f hf s) (hprice (B.origin f) s))
    _=(∑ f∈B.factors,∑ s :bAL,FP (bbD stageDual s) (B.stops f s)) +
        (∑ f∈B.factors,∑ s :bAL,FP
          (fun k=>if moveStart≤ s then freeDual (B.origin f) k else 0) (B.stops f s)) +
        (∑ f∈B.factors,(lineCharge f (B.line f) +
          ∑ s :bAL,FP (residual (B.origin f)) (B.stops f s))) := by
      simp only [FP,envelopePrice,add_mul,sum_add_distrib]
      abel
    _≤_:=add_le_add (add_le_add (stage_bound B) (free_bound B)) (aNI B hline hunit)
end
end qtqUEwc
end
section
set_option autoImplicit true
namespace qtqUEwc
open Finset qUrGXob
open P6_7_3 (IntroIndex introCap)
open qehP9ee (mixedCols)
open P5_7_1 (Ls)
open TD (GM bCb alN FP a3x cSF bf7 ad3
  aa3 running aps XM)
open cu (Shape)
open Ty (aaW aof aoD)
open scoped Classical BigOperators
private def oldN (v :IntroIndex→ℕ) (i:ℕ) :ℕ :=
  ((List.ofFn v).take i).foldl max 0
private def billN (k :Fin 4) (j:Fin 3) :ℕ :=
  ∑ i:IntroIndex,
    let v := fun o=>mixedCols (originShape o) k j
    (max (v i) (oldN v i.val) - oldN v i.val)*introCap i.val j
private theorem cast_fold (j:Fin 3) (L:List (Fin 3→ℕ)) (a :ℕ) :
    (↑(L.foldl (fun n w=>max n (w j)) a) :ℚ) =
      (L.map (fun w l=>(w l:ℚ))).foldl (fun n w=>max n (w j)) (a :ℚ) := by
  induction L generalizing a with
  | nil=>rfl
  | cons w L ih=>simp only [List.foldl_cons,List.map_cons,ih,Nat.cast_max]
private theorem old_cast (v :IntroIndex→Fin 3→ℕ) (i:ℕ) (j:Fin 3) :
    (((List.ofFn (fun o l=>(v o l:ℚ))).take i).foldl (fun n w=>max n (w j)) 0) =
    (oldN (fun o=>v o j) i:ℚ) := by
  rw [List.ofFn_comp' v (fun w l=>(w l:ℚ)),← List.map_take,← Nat.cast_zero,← cast_fold]
  unfold oldN
  rw [List.ofFn_comp' v (fun w=>w j),← List.map_take,List.foldl_map]
private theorem bill_cast (k :Fin 4) :
    resourceBill (fun o j=>mixedCols (originShape o) k j) = ∑ j,(billN k j:ℚ) := by
  unfold resourceBill billN
  simp only [old_cast,Nat.cast_sum,Nat.cast_mul,Nat.cast_sub (le_max_right _ _),Nat.cast_max]
  exact sum_comm
def base :Fin 4→ℕ := ![8395,111824,528999,3163477]
theorem initial_values (k :Fin 4) :initialBound k=(base k :ℚ) := by
  rw [initialBound,bill_cast]
  simp only [← Nat.cast_sum,← Nat.cast_add]
  apply congrArg (fun n:ℕ=>(n:ℚ))
  fin_cases k <;> decide
private def blend (a :GM) (s :Ls) :GM :=
  bCb a (bf7 s.free s.moving s.dI true)
private theorem fold_initial (L:List Ls) (a :GM) (k :Fin 4) :
    (L.foldl blend a) k≤a k := by
  induction L generalizing a with
  | nil=>exact le_rfl
  | cons s L ih=>exact (ih (blend a s)).trans (min_le_left _ _)
theorem bHK {i:ℕ} (hi:i<12) (k :Fin 4) :
    historyAt i k≤ initialBound k := by
  rw [historyAt,dite_eq_left hi,bAW]
  exact fold_initial _ _ _
private theorem after_pair (i:ℕ) (hi:i<12) (L:List Ls) (s :Ls)
    (h: (List.ofFn fun j=>stage (movingStage j)).take (i+1-moveStart.val)=L ++ [s])
    (k :Fin 4) :historyAt i k≤bf7 s.free s.moving s.dI true k := by
  rw [historyAt,dite_eq_left hi,bAW]
  change (((List.ofFn fun j=>stage (movingStage j)).take (i+1-moveStart.val)).foldl
    blend initialBound) k≤_
  rw [h,List.foldl_append]
  exact min_le_right _ _
private theorem fold_min (f :ℕ→ℚ) (L:List ℕ) (a :ℚ) :
    L.foldl (fun n i=>min n (f i)) a≤a := by
  induction L generalizing a with
  | nil=>exact le_rfl
  | cons i L ih=>exact (ih _).trans (min_le_left _ _)
private theorem fold_max_le {a b:ℚ} (L:List ℚ) (ha :a≤b)
    (hL : ∀ x∈L,x≤b) :L.foldl max a≤b:= by
  induction L generalizing a with
  | nil=>exact ha
  | cons x L ih =>
    exact ih (max_le ha (hL x (List.mem_cons_self ..)))
      (fun y hy=>hL y (List.mem_cons_of_mem _ hy))
private def CornersOK (s t:Shape) (r :ℕ) (k :Fin 4) (c:ℕ) :Prop :=
  ∀ x∈[0,aa3 s t],∀ z ∈
      [0,ad3 s t,min (ad3 s t) (s.B-s.J),
        min (ad3 s t) (t.B-t.J)],
    aaW x z k*(r+1)^2+aoD (Ty.aea s x z)
      (Ty.aea t x z) k≤ c
private theorem corner_check (s t:Shape) (r :ℕ) (k :Fin 4) (c:ℕ)
    (hs :aof 1 k=1) (h:CornersOK s t r k c) :
    bf7 s t r true k≤(c:ℚ)/((r+1)^2 :ℕ) := by
  have hc:bf7 s t r true k≤alN s t 1 (r+1) true k :=
    fold_min _ _ _
  apply hc.trans
  unfold alN
  refine fold_max_le _ (by positivity) ?_
  intro q hq
  obtain ⟨x,hx,he⟩:=List.mem_flatMap.mp hq
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp he
  unfold aps
  simp only [Bool.true_or,ite_true,Nat.add_sub_cancel,hs,Nat.cast_one,div_one]
  have hd: (0:ℚ)<((r+1)^2 :ℕ) := by positivity
  apply (le_div_iff₀ hd).mpr
  rw [add_mul,div_mul_cancel₀ _ hd.ne']
  exact_mod_cast h x hx z hz
private theorem after_corner (i:ℕ) (hi:i<12) (L:List Ls) (s :Ls)
    (h: (List.ofFn fun j=>stage (movingStage j)).take (i+1-moveStart.val)=L ++ [s])
    (k :Fin 4) (c d:ℕ) (hd: (s.dI+1)^2=d)
    (hs :aof 1 k=1) (hc:CornersOK s.free s.moving s.dI k c) :
    historyAt i k≤(c:ℚ)/d:= by
  rw [← hd]
  exact (after_pair i hi L s h k).trans (corner_check s.free s.moving s.dI k c hs hc)
local notation "bVi" i=>stage ⟨i,by decide⟩
theorem late_caps :
    historyAt 9 0≤((94442 :ℕ) :ℚ)/((49:ℕ) :ℚ) ∧
    historyAt 10 0≤((145559:ℕ) :ℚ)/((121 :ℕ) :ℚ) ∧
    historyAt 10 1≤((12418826:ℕ) :ℚ)/((121 :ℕ) :ℚ) ∧
    historyAt 11 0≤((263083:ℕ) :ℚ)/((289:ℕ) :ℚ) := by
  refine ⟨after_corner 9 (by decide) [bVi 2] (bVi 4) rfl 0 94442 49 (by decide) rfl ?_,
    after_corner 10 (by decide) [bVi 2,bVi 4] (bVi 5) rfl 0 145559 121 (by decide) rfl ?_,
    after_corner 10 (by decide) [bVi 2,bVi 4] (bVi 5) rfl 1 12418826 121 (by decide) rfl ?_,
    after_corner 11 (by decide) [bVi 2,bVi 4,bVi 5] (bVi 6) rfl 0 263083 289 (by decide) rfl ?_⟩
  all_goals
    intro x hx z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hz
    rcases hx with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;> decide
private def runNat (bw:Fin 3) :ℕ→Fin 4→ℕ
  | 0=> fun _=>0
  | i+1=> fun k=>max (runNat bw i k)
      (if h:i<12 then pI.weight (aHp ⟨i,h⟩) bw k else 0)
private theorem running_cast (bw:Fin 3) (i:ℕ) (k :Fin 4) :
    running (bR bw) i k=(runNat bw i k :ℚ) := by
  induction i with
  | zero=>rfl
  | succ i ih =>
    rw [running,runNat,Nat.cast_max]
    dsimp only
    rw [ih]
    congr 1
    unfold bR
    split <;> rfl
private theorem jump_eq (i:ℕ) (k :Fin 4) (d:ℕ)
    (h:runNat 0 i k+d=runNat 0 (i+1) k) :
    running (bR 0) (i+1) k - running (bR 0) i k=(d:ℚ) := by
  rw [running_cast,running_cast,← h,Nat.cast_add,add_sub_cancel_left]
private theorem projection_fourth (i:ℕ) :running (bR 0) i 3=0:= by
  induction i with
  | zero=>rfl
  | succ i ih =>
    have hz :bR 0 i 3=0:= by unfold bR; split <;> rfl
    rw [running]
    dsimp only
    rw [ih,hz,max_self]
private theorem dot_coords (v a :GM) :
    FP v a=v 0*a 0+(v 1*a 1+(v 2*a 2+v 3*a 3)) := by
  simp only [FP,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl
private theorem flat_bound (bw:Fin 3) {n:ℕ} (hn:n≤12) :
    XM n (bR bw) historyAt≤FP (running (bR bw) n) initialBound:= by
  rw [← cSF n (bR bw) initialBound]
  exact sum_le_sum fun i hi=>a3x (fun k=>sub_nonneg.mpr (le_max_left _ _))
    (bHK ((mem_range.mp hi).trans_le hn))
private theorem flat_cast (bw:Fin 3) (n:ℕ) :FP (running (bR bw) n) initialBound =
    ((runNat bw n 0*base 0+(runNat bw n 1*base 1 +
      (runNat bw n 2*base 2+runNat bw n 3*base 3)) :ℕ) :ℚ) := by
  simp only [dot_coords,running_cast,initial_values,Nat.cast_add,Nat.cast_mul]
private theorem fraction_le (a b c d:ℕ) (hb:0<b) (hd:0<d) (h:a*d≤ c*b) :
    (a :ℚ)/b≤(c:ℚ)/d :=
  (div_le_div_iff₀ (Nat.cast_pos.mpr hb) (Nat.cast_pos.mpr hd)).mpr (by exact_mod_cast h)
private theorem cfP (a b c x y z d e f u:ℕ) (hd:0<d) (he :0<e) (hf :0<f)
    (h:32*(a*x*e*f+d*(b*y*f+c*z*e))≤u*(d*e*f)) :
    (a :ℚ)*((x :ℚ)/d)+((b:ℚ)*((y :ℚ)/e)+(c:ℚ)*((z :ℚ)/f))≤(u:ℚ)/32 := by
  have hd' : (d:ℚ)≠0:=Nat.cast_ne_zero.mpr hd.ne'
  have he' : (e :ℚ)≠0:=Nat.cast_ne_zero.mpr he.ne'
  have hf' : (f :ℚ)≠0:=Nat.cast_ne_zero.mpr hf.ne'
  calc
    _=((a*x*e*f+d*(b*y*f+c*z*e) :ℕ) :ℚ)/((d*e*f :ℕ) :ℚ) := by
      push_cast
      field_simp [hd',he',hf']
    _≤_:=fraction_le _ _ _ _ (by positivity) (by decide) (by simpa only [Nat.mul_comm 32] using h)
private def Az (bw:Fin 3) (i:ℕ) :ℚ :=
  FP (fun k=>running (bR bw) (i+1) k - running (bR bw) i k) (historyAt i)
private theorem bill_succ (bw:Fin 3) (i:ℕ) :
    XM (i+1) (bR bw) historyAt=XM i (bR bw) historyAt+Az bw i:= by
  rw [ XM,sum_range_succ]
  rfl
private theorem projection_row (i a b c x y z d e f u:ℕ)
    (ha :runNat 0 i 0+a=runNat 0 (i+1) 0)
    (hb:runNat 0 i 1+b=runNat 0 (i+1) 1)
    (hc:runNat 0 i 2+c=runNat 0 (i+1) 2)
    (hx :historyAt i 0≤(x :ℚ)/d) (hy :historyAt i 1≤(y :ℚ)/e)
    (hz :historyAt i 2≤(z :ℚ)/f)
    (hd:0<d) (he :0<e) (hf :0<f)
    (h:32*(a*x*e*f+d*(b*y*f+c*z*e))≤u*(d*e*f)) :
    Az 0 i≤(u:ℚ)/32 := by
  rw [Az,dot_coords,jump_eq i 0 a ha,jump_eq i 1 b hb,jump_eq i 2 c hc]
  simp only [projection_fourth,sub_self,zero_mul,add_zero]
  exact (add_le_add (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _))
    (add_le_add (mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _)))).trans (cfP _ _ _ _ _ _ _ _ _ _ hd he hf h)
private theorem base_le {i:ℕ} (hi:i<12) (k :Fin 4) :historyAt i k≤(base k :ℚ)/1 := by
  rw [div_one,← initial_values]
  exact bHK hi k
private theorem close_projection (a b c d cap:ℕ) (h:a+b+c+d≤ cap*32) :
    (a :ℚ)/32+(b:ℚ)/32+(c:ℚ)/32+(d:ℚ)/32≤(cap:ℚ) := by
  rw [← add_div,← add_div,← add_div]
  apply (div_le_iff₀ (by decide : (0:ℚ)<32)).mpr
  exact_mod_cast h
theorem projection_le :cutBook 0≤(projectionFee :ℚ) := by
  have hp:XM 9 (bR 0) historyAt≤((0x6e45e3d40:ℕ) :ℚ)/32 := by
    refine (flat_bound 0 (by decide)).trans ?_
    rw [flat_cast]
    change ((0x3722f1ea :ℕ) :ℚ)≤((0x6e45e3d40:ℕ) :ℚ)/((32 :ℕ) :ℚ)
    simpa only [Nat.cast_one,div_one] using fraction_le 0x3722f1ea 1 0x6e45e3d40 32
      (by decide) (by decide) (by decide)
  have h9:=projection_row 9 16672 317 84 94442 111824 528999 49 1 1 0xd5a80f95
    rfl rfl rfl late_caps.1 (base_le (by decide) 1) (base_le (by decide) 2)
    (by decide) (by decide) (by decide) (by decide)
  have Kr :=projection_row 10 24387 634 166 145559 12418826 528999 121 121 1 0x15b8f2976
    rfl rfl rfl late_caps.2.1 late_caps.2.2.1 (base_le (by decide) 2)
    (by decide) (by decide) (by decide) (by decide)
  have h11 :=projection_row 11 76676 0 0 263083 111824 528999 289 1 1 0x8521f34a
    rfl rfl rfl late_caps.2.2.2 (base_le (by decide) 1) (base_le (by decide) 2)
    (by decide) (by decide) (by decide) (by decide)
  change XM 12 (bR 0) historyAt≤_
  rw [bill_succ 0 11,bill_succ 0 10,bill_succ 0 9]
  exact (add_le_add (add_le_add (add_le_add hp h9) Kr) h11).trans (close_projection _ _ _ _ _ (by decide))
theorem points_le :cutBook 2≤(pointFee :ℚ) := by
  refine (flat_bound 2 (n:=12) (by decide)).trans ?_
  rw [flat_cast]
  change ((0x190213a855:ℕ) :ℚ)≤(pointFee :ℚ)
  exact Nat.cast_le.mpr (by decide)
end qtqUEwc
end
