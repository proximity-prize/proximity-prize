import ProximityPrize.SubmissionLower.ZjZXRjd
import ProximityPrize.SubmissionLower.ZGtaALd
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_2_3Q132
open qfqELEc
def tot:List ℕ→ℕ→ℕ
  | [],_=>0
  | c :: l,q=>Sk q (c % 256) (c/256)+tot l (q+1)
theorem win : ∀ (l:List ℕ) (q:ℕ),Window q l.length (tot l q)
  | [],_=>⟨⟨fun _ _=>0,by simp [tot]⟩⟩
  | c :: l,q=> by
    rw [List.length_cons,Nat.add_comm]
    exact join (row q _ _ _ rfl) (win l (q+1))
theorem w (l:List ℕ) (q r :ℕ) (h:tot l q=r) :Window q l.length r :=h ▸ win l q
set_option quotPrecheck false in
local notation "c!" l=>w l _ _ (by decide +kernel)
theorem c0:Window 0 13 50505:=c! [0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem c1 :Window 13 13 275800:=c! [0,0,0,0,0,0,0,0,0,619,0x2269,0x22367,0x223565]
theorem c2 :Window 26 13 527026:=c! [0x2235663,0x22356661,0x22356675f,0x223566785d,0x2235667895b,0x223566789b59,0,0,0,0,0,0,0]
theorem c3:Window 39 13 601549:=c! [0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem c4 :Window 52 13 515840:=c! [0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem c5:Window 65 13 407785:=c! [0,0,0,0,0,0,0,0,559,558,813,0x452c,0x462b]
theorem c6:Window 78 13 302929:=c! [0x662a,0x8a729,0x8c828,0xcc927,0x114eb26,0x1190c25,0x1992d24,0x229d6e23,0x23218e22,0x3325af21,0x453add020,0x46431d11f,0x20100c0a363325db0f91f]
theorem c7:Window 91 13 209203:=c! [0x20100c4a563b2ddd1091e,0x10080625332198ee81e,0x1008063533259aef81d,0x804232a9d96ce71d,0x8042332a198ce71c,0x402199952cd61c,0x422299d56ce61b,0x21118d0ac61b,0x21918d2ad61a,0x11148e6b51a,0x1118906c519,0xc8c49319,0x10148e4b318]
theorem c8:Window 104 13 131653:=c! [0x80c48218,0xc0c49217,0x80a07217,0x80c08216,0x606016,0x80a07015,0x406015,0x606014,0x405014,0x406013,0x3013,0x405012,0x2012]
theorem c9:Window 117 13 72460:=c! [0x3011,0x2011,0x800110,0,0x84020f,271,0x4030e,0x4020e,0x808040d,0x4030d,0x201008050c,0x808040c,0x20180c060b]
theorem c10 :Window 130 13 32150:=c! [0x201008050b,0x4040200e070a,0x20180c060a,0x1008040280e4809,0x4040200e4709,0x100c06230124908,0x1008042280e4808,0x20211007238146a07,0x110c06230126907,0x884021140734016ab06,0x82021100733814aa06,0x4000886031980954816cc05,0x4000884021940754016cb05]
theorem c11 :Window 143 13 9355:=c! [0x2000041010c803a9c0a6501acd04,0x2000040008c6032980964816cc04,0x1000020004620114a03b200b6581cee03,0x1000020000610114803b1c0a6501aed03,0x80001000030004a30198c04b240b7601f0f02,0x80001000030004a20118a03b200b7581d0e02,0x4000080001800050808c401d8e053a80d868213001,0x4000080001800050004c30198c04ba40b8601f2f01,0x2000040000c0002800261008c501dd005c2c0e970217100,0x2000040000c0002800060808c401dce054280d968217000,0x2000040000c0002800060004c3019cc04c240b9601f6f00,0x2000040000c0002800060004c2011ca03c200b9581d6e00,0x2000040000c0002800060000c1011c803c1c0a9501b6d00]
theorem c12 :Window 156 9 966:=c! [0x2000040000c0002800060000c0009c60341809948176c00,0x2000040000c0002800060000c0009c40241407940176b00,0x2000040000c0002800060000c0001c20241007938156a00,0x2000040000c0002800060000c0001c00140c06930136900,0x2000040000c0002800060000c0001c001408049280f6800,0x40000c0002800060000c0001c000404049200f6700,0xc0002800060000c0001c000400029180d6600,0x2800060000c0001c00040002910096500,0x60000c0001c00040000908096400]
theorem proof :qPQ4nYa.c3:= by
  obtain ⟨p,hp⟩:=(join c0 <| join c1 <| join c2 <| join c3 <| join c4 <| join c5 <| join c6 <| join c7 <| join c8 <| join c9 <| join c10 <| join c11 <| c12).witness
  refine ⟨p,?_⟩
  change (∑ q∈Finset.range 165,gradeSum q (p q))≤3137221
  simpa only [Nat.zero_add] using hp.le
end P5_7_2_3Q132
end
section
set_option autoImplicit true
namespace qkgz7gb
open P5 (p)
open P5_7_3 (fO)
open Dt (jJ)
private def ordinateMultiplier (e :ℕ) :ℕ→ℕ
  | 0=>0
  | 1=>e-1
  | 2=>e
  | 3=>2*e
  | 4=>3*e
  | 5=>5*e
  | 6=>8*e
  | 7=>12*e
  | 8=>20*e
  | _=>32*e
private def ratio (i:ℕ) :ℕ :=
  [2,4,8,12,16,24,32,48,64,96,128,256,512,1024][i]?.getD 0
private def decode (D e u n:ℕ) :Witness :=
  let g:=ordinateMultiplier e (n%16)
  let E :=e+g
  let asym:=n/1024%2=1
  let i:=n/16%4
  let k :=n/64%16
  let scale :=if asym then [100,130,175,250][i]?.getD 0 else [100,125,150,200][i]?.getD 0
  let s :=if asym then Stock.asymmetric ((p-1-E*u)/e-u) (ratio k*u)
    else Stock.symmetric (4*2^k*u)
  ⟨g,E*D*scale/100+1,n/2048,s⟩
private instance (D e u:ℕ) (w:Witness) :Decidable (FilterOK D e u w) := by
  unfold FilterOK
  infer_instance
private instance (D e W:ℕ) (s :Stock) :Decidable (CurveOK D e W s) := by
  cases s <;> unfold CurveOK <;> infer_instance
private theorem checked {D e u cap:ℕ} (n:ℕ)
    (h₁:FilterOK D e u (decode D e u n))
    (h₂:CurveOK D e (decode D e u n).weight (decode D e u n).stock)
    (h₃:0<smoothRate D e u (decode D e u n).weight (decode D e u n).stock)
    (h₄:2*smoothRate D e u (decode D e u n).weight (decode D e u n).stock<p)
    (h₅: (highStock e u (decode D e u n)).b5A +
        planeFee (smoothRate D e u (decode D e u n).weight (decode D e u n).stock)≤ cap) :
    Ready D e u cap :=
  ⟨decode D e u n,h₁,h₂,h₃,h₄,h₅⟩
private def E5 (D cap:ℕ) :ℕ→List jJ→Prop
  | _,[]=>True
  | e,g :: gs=>Ready D e g.seedCap cap∧E5 D cap (e+1) gs
local notation "r!" n=>checked n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem evu:E5 (wX .h2704) (fO.schedule .h2704).retainedFee 1
    (fO.schedule .h2704).gw :=
  ⟨r! 0x1c15a030,r! 0x4c16a031,r! 0x7c179031,r! 0xac187831,r! 0xa1ee7061,r! 0xc2a7f062,
   r! 0xba1e4093,r! 0xd5799093,r! 0xd05258c4,r! 0xe7c530c4,r! 0xff40c0c4,r! 0xfc7d1104,
   r! 0x110a85105,r! 0x125b95905,r! 0x123673145,r! 0x136ee6145,r! 0x14a7be945,r! 0x15e072945,
   r! 0x15eb05186,r! 0x1712ba686,r! 0x183ad1686,r! 0x1962e0686,r! 0x1a8aea686,r! 0x1bb31ae86,
   r! 0x1cdbf1186,r! 0x1e0421186,r! 0x1f2c4a186,r! 0x221674945,trivial⟩
private theorem r2708:E5 (wX .h2708) (fO.schedule .h2708).retainedFee 1
    (fO.schedule .h2708).gw :=
  ⟨r! 0x1c160030,r! 0x4c179031,r! 0x7c192031,r! 0xac1aa031,r! 0xa1f09061,r! 0xc2aa8062,
   r! 0xba20b093,r! 0xd57c6093,r! 0xd05520c4,r! 0xe7c848c4,r! 0xff4420c4,r! 0xfc807104,
   r! 0x110abf905,r! 0x125bd4905,r! 0x1236b1945,r! 0x136f28945,r! 0x14a805145,r! 0x15e0bd945,
   r! 0x171958145,r! 0x171306e86,r! 0x183b22686,r! 0x196337686,r! 0x1a8b47e86,r! 0x1ab9846c7,
   r! 0x1bd7016c7,r! 0x1cf4796c7,r! 0x1f2cb7186,r! 0x2054df186,r! 0x217cff986,r! 0x2771ee105,trivial⟩
private theorem r2715:E5 (wX .daC) (fO.schedule .daC).retainedFee 1
    (fO.schedule .daC).gw :=
  ⟨r! 0x1c168030,r! 0x4c18e831,r! 0x7c1b5031,r! 0xac1da831,r! 0xa1f38861,r! 0xc2ae1862,
   r! 0xba243893,r! 0xd5806893,r! 0xd05918c4,r! 0xe7ccb0c4,r! 0xff4900c4,r! 0xfc854904,
   r! 0x110b13105,r! 0x125c2e105,r! 0x12370a945,r! 0x136f88145,r! 0x14a86a145,r! 0x15e128945,
   r! 0x1719c9145,r! 0x171373686,r! 0x183b94686,r! 0x1963ade86,r! 0x1a8bc2e86,r! 0x1bb3fee86,
   r! 0x1cdc30e86,r! 0x1e051b986,r! 0x1f2d4e986,r! 0x20557a986,r! 0x23501b145,trivial⟩
private theorem r2725:E5 (wX .daF) (fO.schedule .daF).retainedFee 1
    (fO.schedule .daF).gw :=
  ⟨r! 0x1c17c830,r! 0x4c1c6831,r! 0x7c20f831,r! 0xac258031,r! 0xa1fb2061,r! 0xc2b74062,
   r! 0xba2d0893,r! 0xd58a8893,r! 0xd06308c4,r! 0xe7d7c0c4,r! 0xff5528c4,r! 0xfc915904,
   r! 0x110be3105,r! 0x125d0e905,r! 0x1237e9945,r! 0x137075945,r! 0x14a967145,r! 0x15e234945,
   r! 0x15ec52686,r! 0x171488686,r! 0x183cb5e86,r! 0x1964dc686,r! 0x1a8cfe686,r! 0x1bb546e86,
   r! 0x1cde42186,r! 0x1e0689986,r! 0x20e076945,r! 0x22190e945,trivial⟩
private theorem r2750:E5 (wX .rQ) (fO.schedule .rQ).retainedFee 1
    (fO.schedule .rQ).gw :=
  ⟨r! 0x1c192030,r! 0x4c200031,r! 0x7c26e031,r! 0xac2da831,r! 0xa202d861,r! 0xc2c08062,
   r! 0xba35f093,r! 0xd594b893,r! 0xd06d00c4,r! 0xe7e2d0c4,r! 0xff6160c4,r! 0xfc9d6904,
   r! 0x110cb4105,r! 0x125def905,r! 0x1238c8945,r! 0x137163945,r! 0x14aa64145,r! 0x15e340945,
   r! 0x15ed5de86,r! 0x1715a1686,r! 0x183ddce86,r! 0x196611e86,r! 0x1a8e41686,r! 0x1bb697e86,
   r! 0x1cdfa3986,r! 0x1e07f9186,r! 0x20e205945,r! 0x24d2c9905,trivial⟩
private theorem r2775:E5 (wX .daL) (fO.schedule .daL).retainedFee 1
    (fO.schedule .daL).gw :=
  ⟨r! 0x1c1a0030,r! 0x4c224031,r! 0x7c2a6831,r! 0xac327831,r! 0xa2092861,r! 0xc2c84062,
   r! 0xe55c5062,r! 0xd59e2093,r! 0xf1012893,r! 0xe7ed88c4,r! 0xff6d28c4,r! 0x116dba0c4,
   r! 0x111f33104,r! 0x125ecd105,r! 0x13b0dc905,r! 0x1502a2105,r! 0x14ab60145,r! 0x15e44b145,
   r! 0x171d18145,r! 0x1855cc145,r! 0x198e78945,r! 0x19673b686,r! 0x1a8f7d686,r! 0x1bb7e7686,
   r! 0x1ce049686,r! 0x1e08a2e86,r! 0x1f30f5e86,r! 0x205941e86,r! 0x218274986,r! 0x22aac3186,
   r! 0x23d31f986,r! 0x26ff8b145,trivial⟩
private theorem ezJ:E5 (wX .sY) (fO.schedule .sY).retainedFee 1
    (fO.schedule .sY).gw :=
  ⟨r! 0x1c1f3830,r! 0x4c305031,r! 0x7c415831,r! 0xac524031,r! 0xd7b72022,r! 0xc2ecf862,
   r! 0xe5877862,r! 0xd5c6b093,r! 0xf12ee893,r! 0xe819c0c4,r! 0xff9dd8c4,r! 0x11710c8c4,
   r! 0x112278104,r! 0x127738104,r! 0x13b49e905,r! 0x1506a3105,r! 0x16585f905,r! 0x15e6c6e05,
   r! 0x172180945,r! 0x185a6e145,r! 0x1b9ff9905,r! 0x1cf1f4905,trivial⟩
private theorem r2900:E5 (wX .s4) (fO.schedule .s4).retainedFee 1
    (fO.schedule .s4).gw :=
  ⟨r! 0x1c1f9030,r! 0x4c310831,r! 0x7c425831,r! 0xac537831,r! 0xd7ae7822,r! 0xc2f1b862,
   r! 0xe58c9862,r! 0xd5cd3893,r! 0xf1365093,r! 0x10caea893,r! 0xffa678c4,r! 0x1171a18c4,
   r! 0x12ea628c4,r! 0x1461ad0c4,r! 0x13cda7104,r! 0x15075b905,r! 0x153b07dc5,r! 0x17ab1f905,
   r! 0x18fd3f905,r! 0x1a4f0b905,r! 0x1ea8000c4,trivial⟩
private theorem r2919:E5 (wX .h2919) (fO.schedule .h2919).retainedFee 1
    (fO.schedule .h2919).gw :=
  ⟨r! 0x1c20e830,r! 0x4c34a031,r! 0x7c482831,r! 0xac5b8031,r! 0xd7b6b022,r! 0xc52f9861,
   r! 0xe597d862,r! 0xd5d80893,r! 0xf1428093,r! 0x10cbc3893,r! 0xffb380c4,r! 0x1172858c4,
   r! 0x12eb5a0c4,r! 0x1462b80c4,r! 0x13ceac104,r! 0x150871105,r! 0x153c20dc5,r! 0x17ac5a905,
   r! 0x18fe8f905,r! 0x1a507b905,r! 0x1ba228905,r! 0x2021128c4,trivial⟩
private theorem r2946:E5 (wX .h2946) (fO.schedule .h2946).retainedFee 1
    (fO.schedule .h2946).gw :=
  ⟨r! 0x1c20f030,r! 0x4c349831,r! 0x7c481831,r! 0xac5b6031,r! 0xd7b35822,r! 0xc5305061,
   r! 0xe598a862,r! 0xd5d94893,r! 0xf143e893,r! 0x10cbdc893,r! 0xffb540c4,r! 0x1172a30c4,
   r! 0x12eb790c4,r! 0x1462d88c4,r! 0x15db8b0c4,r! 0x151fc3d84,r! 0x1678c9104,r! 0x17ac7a105,
   r! 0x18fea3105,r! 0x1d32f38c4,r! 0x239282893,trivial⟩
private theorem r2950:E5 (wX .s5) (fO.schedule .s5).retainedFee 1
    (fO.schedule .s5).gw :=
  ⟨r! 0x1c228030,r! 0x4c38e031,r! 0x7c4f1031,r! 0xac651031,r! 0xd7bf0822,r! 0xc53b8061,
   r! 0xe5a5a862,r! 0xd5e58093,r! 0xf151b093,r! 0x10ccd1093,r! 0xffc3e0c4,r! 0x1173a20c4,
   r! 0x12ec8d8c4,r! 0x1464020c4,r! 0x15dcca0c4,r! 0x1520f8584,r! 0x167a11904,r! 0x17add2105,
   r! 0x19255c104,r! 0x1d34560c4,r! 0x2af44a062,trivial⟩
private theorem r2980:E5 (wX .tI) (fO.schedule .tI).retainedFee 1
    (fO.schedule .tI).gw :=
  ⟨r! 0x1c236030,r! 0x4c3b1831,r! 0x7c52a031,r! 0xac69e831,r! 0xd7c1c022,r! 0xc5422861,
   r! 0xe5ad5862,r! 0x10885b062,r! 0xf15a6893,r! 0x10cd6c093,r! 0x12851e093,r! 0x1174470c4,
   r! 0x12ed3e8c4,r! 0x1464be0c4,r! 0x147788544,r! 0x1755758c4,r! 0x18cdaa8c4,r! 0x1a45a50c4,
   r! 0x1bbc190c4,trivial⟩
private theorem eGP:E5 (wX .s6) (fO.schedule .s6).retainedFee 1
    (fO.schedule .s6).gw :=
  ⟨r! 0x1c25f030,r! 0x4c41f831,r! 0x7c5dd831,r! 0xac797031,r! 0xd7d2f022,r! 0xc5548061,
   r! 0xe5c29062,r! 0x1089e3062,r! 0xf1712893,r! 0x10cf00893,r! 0x1286dc093,r! 0x1175ee8c4,
   r! 0x12ef0a0c4,r! 0x1466ad0c4,r! 0x147979d44,r! 0x1757aa8c4,r! 0x18d0048c4,r! 0x1a48270c4,
   r! 0x1bbf098c4,trivial⟩
private theorem r3050:E5 (wX .tT) (fO.schedule .tT).retainedFee 1
    (fO.schedule .tT).gw :=
  ⟨r! 0x1c283830,r! 0x4c481831,r! 0x7c67a831,r! 0xac870031,r! 0xdca5e831,r! 0xc565c861,
   r! 0xe5d69862,r! 0x108b51062,r! 0xf1874893,r! 0x10d089893,r! 0x128887893,r! 0x11778c8c4,
   r! 0x12e2d6504,r! 0x1468828c4,r! 0x15e1870c4,r! 0x1759868c4,r! 0x18d14f0c4,r! 0x25770f062,trivial⟩
private theorem r3100:E5 (wX .s7) (fO.schedule .s7).retainedFee 1
    (fO.schedule .s7).gw :=
  ⟨r! 0x1c2d3830,r! 0x4c557831,r! 0x7c7d6831,r! 0xaca4e031,r! 0xdccbe831,r! 0xc589e061,
   r! 0xe6006862,r! 0x108e52062,r! 0xf1b47093,r! 0x10d3a9093,r! 0x128bf1893,r! 0x14441f093,
   r! 0x12e64c504,r! 0x146c360c4,r! 0x15e53d0c4,r! 0x1b1e66893,trivial⟩
private theorem r3200:E5 (wX .sJ) (fO.schedule .sJ).retainedFee 1
    (fO.schedule .sJ).gw :=
  ⟨r! 0x1c373030,r! 0x4c702831,r! 0x7ca8a831,r! 0xace0b031,r! 0xdd183031,r! 0x108f2a022,
   r! 0xe6540062,r! 0x109451862,r! 0x12c354862,r! 0x10d9ec093,r! 0x1292d7893,r! 0x144ba4893,
   r! 0x1414204c4,r! 0x1473e50c4,r! 0x19747c093,r! 0x1b2a19093,trivial⟩
private theorem c6q:E5 (wX .tv) (fO.schedule .tv).retainedFee 1
    (fO.schedule .tv).gw :=
  ⟨r! 0x1c3e0830,r! 0x4c822831,r! 0x7cc57831,r! 0xad07e031,r! 0xdd495031,r! 0x109052022,
   r! 0xe91a1061,r! 0x10988b062,r! 0x12c808062,r! 0x10de89093,r! 0x12bec6493,r! 0x1450da093,
   r! 0x160975893,r! 0x17c0bb893,r! 0x1fb0b1862,trivial⟩
private theorem r3555:E5 (wX .uH) (fO.schedule .uH).retainedFee 1
    (fO.schedule .uH).gw :=
  ⟨r! 0x1c549830,r! 0x4cbeb031,r! 0x7d27e831,r! 0xad8f9031,r! 0xddf5b031,r! 0x10e591031,
   r! 0xe9d6d061,r! 0x10a5c9062,r! 0x12d6a9062,r! 0x14f314452,r! 0x1735b4862,r! 0x195e80062,trivial⟩
end qkgz7gb
end
