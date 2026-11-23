import ProximityPrize.SubmissionLower.KoalaAt2428Gate17
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate18
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨134,56,12,134,56,3484,4434,⟨10240934033,53999518299,12829396562⟩,4379358849162⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919968344960
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05t,unpack 2 0x4a0c574159983ca,unpack 3 0x4a4d9a44a0c16e17f649e2,b04j,b03j,b02j,b02k,b01d,
  b01g,b00c,bz1,bz7,bxs,unpack 9 0x24c5ca925c930f2587ef02546ec325672d52526ad024e64b50730efa946,unpack 10 0x26abf352464ebb2649f062567ee52566ece25672ec2506eb52505cca03334c6f5e,bw8,
  unpack 10 0x2506ac3262970b24e5ec525880e225a7eec2526cc62526ac625062ba073805d042,unpack 11 0x13666ac9272c511314e9712a396292c3f7412a346a129396612a3663839b3a0c6ede,unpack 12 0x266ad30264ad102484ec2266a51825a86e325470cf25064ca25676d725260d024e64b7033c6934f6,unpack 13 0x123245413d73b99293c7392c3b6992d437612d407b92a3b6912c386d1283465929376281873ec5cfc2,unpack 14 0x123245412d3f7413970b91262c531304984129356612d407192b3c6e12a3a6c12a366912934610383412295da,unpack 15 0x1232454125265113458961335d99128295113155991282b5512c457892b377312a3e6212a356b9293169018b427cabc3,unpack 15 0x1252651124255113a71bc9314872925295a9345793929396b929346a12e4375928356392a356b9293461858d4585fa8e,bp1,
  unpack 16 0x1242551124274f933559c139669e123265b9304c7f12c3d6b12d417712b3d6f12a346b1293763127336b12b375b83834a3f5b72,unpack 17 0x12b3e71924274f925245093a71ba9304c8a9262c531365d97125275812f4b7992b3675929396112b38691283361129326a018b4b99715b,unpack 17 0x124274f925245092c407093c72b7928377012828531335c9c1272c5612f488092a3c6f92a346b12b39691293665928325e05834df63773,unpack 18 0x12f4e839252450923235413559971386dad128285312839739324f7e929386a12c3a6b92a3d6f92d4074129326792934629253162819550ff5af2,unpack 18 0x1b5232354125265113d75b293353939252a5892f4c8892b3c6e93048781252c5e92c3d7012c3f6a12a356c1263366928325e8a83535c210a,unpack 19 0x1345b969232354125265112c3e7313d77b392c3d781242a591365c9a1262f5712f478392b386892b3b6c92933661273768928356292b3160018755b8bbd6,unpack 19 0x1293c7092526511242651935599793c73b59242a591282a5113461a01272c5e92f478492c3f6992b38691293466925346412b3464929325e838b5712d1bf,unpack 20 0x13767ad12526511242651925255113a73b69365e9e9282a511283a6e93353901262a5512f488412d416e12a356b925346412d3a6a928325e9292f668583596f97d7,
  unpack 20 0x9725c20921328c9292a8896a13709cb7dfc99253c49294ad897a4c2896a2b9c951d35c959d360969ebb8939d364969c35c949baf89519b5c2c1955c78bb56,unpack 21 0x1396db51272f5d12525511242749935589a93c72b51283368125294f1345ba4129336092e4878129316992b3e6a12a376f928396e12c35629253163129325f0a835ed5816e,unpack 21 0x1325a9812525511242749925255693c70b513868ac125294f124295f13965a59262d5f1314c829262a5412c426f12a376f928386e1293567928325e92b3160819d6085bed3,unpack 22 0x9db7d70951dbbc9213a4c9292ab4959f3749e395c89928c449214af8959db509a2bcd4931629c98a5418941b314951c358959f3b4951aadc9399b6c961ab300ce9b628c5d6f,unpack 22 0x9bb455c9213a4c9292ab491912a09a2dc709eb9dd0949d39892932b89927c1c9724bec9396ac497a4bf096a13d0951ab28939a384959aaec949a33c951bb2474d8d6595ac3a,unpack 23 0x9db7d709725c1c9292ab491912a092132889eba5889cb75c892932b89417a689a2ecf4959cb70949a31896a03dc96a2394939ab4c951ab60961bb3494192f4941ab5c6c68767f24706,unpack 23 0xa13a4bc8f14ba091912b4921328896a0b609f39de4982bc8894162a49314ad89cb6d8c9293ab49723bc4951b340961f3ac951d304941bb94961a334939a358941a2ec343836a4f0d1e,unpack 24 0xa9b84e09c2e48c8493ac0908eb509393a5c99ad4b89f3b52895a1bf89313314949d3709aad4d09294ad899aa42c931529c96a0bd8941b374959b308949c388941bb14959aac81c18b6ba92307,
  unpack 24 0x4dd7244ae8715aa08f8eb6c9193a909f3c5389f3ec9c9212b80929239c98a6c0096254089393b409928c0493172b89720be8951d340949933c941cb78959c2f4949833c0c5876e05bdd3,unpack 25 0x266a30531ae951c31c8412b08961ebd4a1bdc9ca9b0cb083982e4908e3c49c353d89399c38921234899284609499360949c3b0969e320959e3709419ad4949a3689499afc2c38d710f0c9e,unpack 25 0xc58d74bd19d8424a9464ed6638559ceb26284192789091360a03c43491133b894994109721c00949e3a49295b94959bb90961db74949b34094192f893193241c69d72bf4a03,unpack 25 0x31635d8a4058ab28ae5573162961e34887a1b20aaadcf081192ac97a43c49416c0c97224049215bd0959bb949297bd4961b31c9299320949834034e9575c86d82,unpack 25 0x62c6bb1635d8b1ae9825be09a29c28841c2b498a8c289094aec9721c04949a4209217b9095173d09297bd8941833c959aacc74a8b7722836b,unpack 25 0x18b1aec58d762c6bb16297a1b9099a9428811f22896a0418949bbe092163d09396bf094173f49416b809398b3454583797f4983,unpack 25 0x62c6bb1635d8b1aec58d762961eb5c85a7b38941e308931840c9396bf09296c1894153c09397375e41957c886d02,b0e,
  b0g,unpack 25 0x18b1aec58d762c6bb1635d8b1aec5304a7a107495c121386712523779242883adbb488ad92829c3a67,unpack 25 0x62c6bb1635d8b1aec58d762c6bb16298a4bd07f27a409392bc892953ed9ddc185a58932,b0o,b0q,bq.take 4++unpack 21 0x62c6bb1635d8b1aec58d762c6bb1635d8b19625498f,bs.take 3++unpack 22 0x31635d8b1aec58d762c6bb1635d8b1aec58d79c8e73f9,unpack 25 0x18b1aec58d762c6bb1635d8b1aec58d762c6ba1e9f0123486625d95824cd4,
  [],[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 14 then [] else boxesTape.getD (r-14) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","!$","!$(",
  "!#'","!#'-","!#&*3","!#&+4","!#&+/8","!#&)/5","!#%*06B","!#&*17DB",
  z5k,"!#%)-38FO",z59,"!#%(.3;JH`","!#%(,4<DJW","!#%(,4==KO",z67,"!#%'-05>OM_s",
  "!#$(+06?IOVws","!#$'+16@CQOows","!#$'+17A@SQg{ws",z3w,"!#$&*.48BOUVw~#!{t",z4B,z64,"!#$&*/3:FDZY^~#!~#*~#&~#!",
  "!#$&),4;AFTZYv~#-~#*~#&u",z3K,"!#$&)-17;HH_]f~#)~#1~#-~#*u",z31,(zz93 ++ "~#-u"),z2u,"!#$&),16>@KNece~#)~#=~#9~#5~#/u",z4m,
  "!!#%(,/7;?MLageu~#8~#A~#=~#9~#/u","!!#%(,/47@NMZhgm~#0~#D~#A~#=~#9~##","!!#%(*/38@INSkhg~#(~#H~#D~#A~#=~#/u","!!#%(+/38AEONlkh}~#@~#H~#D~#A~#:~##","!!#%'+/39BAPOflku~#8~#L~#H~#D~#A~#/u","!!#%'+049CBRP`nlm~#0~#P~#L~#H~#D~#5~##","!!#%'+-4:?CSRYpnl~#'~#H~#P~#L~#D~#5~#'u",(zz103 ++ "n}~#@~#T~#P~#D~#5~#'u"),
  "!!#%'*.17:DITSlrnj~#7~#X~#R~#D~#5~#'u","!!#%'*.15;EDUTftni~#$~#N~#R~#D~#5~#'u","!!#%'*.15;FEVT[tnin~#;~#R~#D~#5~#'u","!!#%'*.15<FEWTRtnic~#(~#R~#D~#5~#'u","!!#$&),16<BEPTQjnicr~#?~#D~#5~#'u","!!#$&),26==EITQ`nic`~#-~#D~#5~#'u","!!#$'),26=;ECTQVnic^w~#D~#5~#'u","!!#$'),/68;ECTQNnic^d~#1~#5~#'u",
  "!!#$&)-/35;ECTQNeic^W{~#5~#'u","!!#$&(-/15;ECMQNZic^Wh~#5~#'u","!!#$&(+/15;@CFQNPic^WT~#!~#'u","!!#$&(+/15;;CAQNKic^WRl~#'u","!!#$&(+/15;:CAQNK_c^WRY~#'u","",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 6, 8, 12, 15, 19, 25, 23, 32, 30, 45, 42, 39, 48, 62, 56, 51, 45, 40, 71, 75, 61, 46, 32, 17, 2]
  | 71 => [0, 0, 1, 2, 4, 5, 8, 10, 15, 19, 21, 24, 33, 31, 40, 43, 40, 40, 64, 58, 53, 48, 42, 58, 81, 67, 52, 37, 23, 8]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'+,154:CACNKHc^WRLJugWH:+"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9726995086445 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8449417175140 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 23 = 2566304244796 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20742716506381 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20742716506381 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9726995086445 exactLoss0
      |>.append 24 8449417175140 exactLoss24
      |>.append 23 2566304244796 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20742716506381,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate18

#print axioms KoalaAt2428Gate18.loss_bound
#print axioms KoalaAt2428Gate18.receipt
