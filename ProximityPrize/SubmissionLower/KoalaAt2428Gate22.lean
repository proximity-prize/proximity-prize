import ProximityPrize.SubmissionLower.KoalaAt2428Gate21
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate22
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,56,11,136,56,3536,4436,⟨9760473411,48600685254,34018809543⟩,4233688324359⟩
abbrev split:ℕ:=64
abbrev unit:ℕ:=1919968419840
abbrev terminal:ℕ:=72
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05q,b04z,b050,b048,b03c,b02l.take 3++unpack 1 0x18a31b0a,b01e.take 3++unpack 2 0x4a4e1801aa99cb6,b01h,
  unpack 6 0x25678dd25676d925268d524e5cc40327d2e3ae,bz2.take 3++unpack 4 0x4b51e0e4acf1c04b0e9bc22161696,bz9,bxt.take 4++unpack 4 0x4bd2a204a4dda04acf1a8236fe420,bxy,by4,bwa,unpack 10 0xf5304b849272d6092c407112d3f769293560129356381873805d042,
  unpack 10 0x1272b4f9304d9592a396292b3d7192a356a12a39661293360839b3a0c6ede,unpack 11 0x13255869242761132518a92c426e92b3a6b128326592b386892931688d833c6934f6,unpack 11 0x12a3e7612b3a6812d447612d3f7c12a3b6912b376a9293365928355f01873ec5cfc2,bsf.take 5++unpack 7 0x4e5bee0494a9444c12e124a4c98e4b915de4a8e1a232f61c82,brd.take 4++unpack 9 0x4d15e4e4c966544a0a9444c54e5c4a0b1544b111e24acddce4a8fd8838b3067a,unpack 14 0x124254f93a6eba1304770126295b1335691129396b929336a92d4475929356412a356b928315d858d4585fa8e,bp1.take 4++unpack 11 0x490953e4b4f9ce4edc6bc4a0bd8a4a4edb84bd1a084b505dc4a8e5984a8ddba4a8e99c3dc2c8b7,bp5,
  unpack 16 0x124264f925245193a71ba1304b889252b509365a949262c5e92e477312b3675929396192b386912833611282f66018b4b99715b,unpack 17 0x921327c929228c96203749db7da4941c3809413a989a2fd009396ab496a1bcc959e37c951a35c959cb4c949bb2c0c5834df63773,unpack 17 0x929228c9212aa09a2b4a09bb65589413a98949e3bc99283f8949ab34959db60951d36096a03a4949933c949ab142c19550ff5af2,unpack 18 0x4a0c186490955049095464f1cebc4cd4646498ad644bd36244acf1ba4b915d449cbd8a4ace9b24b509b842931a3380ca83535c210a,unpack 18 0x9212aa09212a8c961f38c9eb9d7c961f3c491952c89b2e4d89397ab897a4420951ab24959db64949a334939bb44949ab185418755b8bbd6,unpack 19 0x959fb9c9212a8c92932909a2bc9c9db858492162e494962a49a2fcec93152d897a3c24961fb50959cb489418310931c348961a3240c38b5712d1bf,unpack 19 0x9212a8c92932909212a789d395ac9aae4e094962a4941c35c9928c689316ac897a2c0096a1374951a35c931c348961bb3094992f41c583596f97d7,unpack 20 0x97a6c3c92932909212a7896a13749cb75f499253c89293abc972543096a2ba0951bb3c961f384961cb98939d368969c358949c2fc9497b342c1955c78bb56,
  bg5.take 5++unpack 15 0x4a0c17e490953c494a1304d15e664edbec04a4cda0498b14e4cd66844a0cd824b915d24a4c5a44acfdaa4a8ddbe4a0e1ba50ffcebd,bga,unpack 21 0x4a8f1e2494a13049091524b105c84f1bad24c94a2848c996e4acf1aa4cd525a49cbd604c11dfc4a4e99e4a4d19a4acf9da4a8d96e4a4ddce2a0ce9b628c5d6f,unpack 22 0x4e1aab6494a1304909152490915c4d16a324f1bed44a4e9ce494a96c4c525f04bd3208498ad504c1320c4b0f9d84a8d9944a0e1d84a8c5604ace5b60674d8d6595ac3a,unpack 22 0x4bd2e3e4909152490915c49099464f1cab24e5aedc494a96c4a0b1264cd6a6a4ace9b84a8dda04b501f04b105b84a0e1ba4a4c99e4b0dd9a4a8dd923a6c68767f24706,unpack 23 0x50dd658478b1e6488799249099464b101a84f5c2dc4c566564a0a946498a56a4e1aeb8498a56e4b515d24a8d59e4b0fdd84a8e9824a0ddcc4b0d19a4a0d5ae36343836a4f0d1e,unpack 23 0x4e17a4c428ad8248065d6498992e4cd62564f5d6744b10e14498998a4a0e9ba4d96a6c494a96c4c9420449cb9644b0f9d84a4e9d04acd9864a0d1ae4a4e18c1a1c18b6ba92307,unpack 24 0x134558894a2474d023e36dc24446bd27aef3f27cf71824a50fd2463cd92629b0025a9b0b24e50d1264a30224a56a425c82fa25474d12546cda454b0e57a0e0c5876e05bdd3,
  unpack 24 0x8a94b101be428a9a64a8e9ea511f244545663441cc1b24887df44dd9ddc4a0de2e49091a64c5361e4a8c9b24a0e1d84b4f1904acf1ba4a0d1684a8d1b6062c38d710f0c9e,b1t,b1z,b26,b2e,b2n,b0e.take 5++unpack 19 0x1152448a9224549122a48914b905c442d39d8498fd724a4d1fc4909a12751be3ea,b0g.take 6++unpack 18 0x8a9224549122a489152448a94b915d8415299e4a909a4767593e3,
  b11.take 5++unpack 19 0x4549122a489152448a922454914b915d642539a2484e19c7ad9240c,b12.take 5++unpack 19 0x22a489152448a9224549122a48914bd11d440151507de29e13,b0o.take 5++unpack 19 0x1152448a9224549122a489152448a949911d08c072ee0,b3x,b3r,b46,b4c,[],
  []]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 15 then [] else boxesTape.getD (r-15) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","!$",
  "!$","!#'","!#&+","!#'+","!#&,/","!#&*05","!#&*07","!#&*18E",
  "!#%)-9?E","!#%).49F","!#%).3:HH","!#%(/3;JH","!#%(,4<DJX","!#%),5=>LO","!#%(-19=NL","!#%(-06?PN`",
  "!#%(+16@JPW","!#%'+17ADRPp","!#$',28BATRh|","!#$',.8=BVT`~##|","!#$'*/48CPVWx~##|","!#$'*/39DIXVp~#'~##|","!#$'*/4:EDZXh~#+~#'~##","!#$&+04;FE[Z_~##~#+~#'~##",
  "!#$&)-5;AFU[Zw~#/~#+~#'","!#$')-5<=HO^[o~#2~#/~#+~#$",z5h,"!#$&*.16=JIb`_~#!~#6~#2~#/~#$","!#$&).16>KJ[b`w~#:~#6~#2~#/","!#$&),27>FKUdbo~#2~#:~#6~#2~#$","!#$&),27?ALOfdg~#*~#>~#:~#6~#0","!#$&),28@?MLhfd~#!~#B~#>~#:~#6~#$",
  "!#$&(-/8<@NMbhfw~#:~#B~#>~#:~#0","!#$&(-/58AON[jho~#2~#F~#B~#>~#:~#$",z4Y,"!#$%(+049BFPOnlj~#!~#A~#J~#F~#B~#<~#$","!#$%(+04:CBRPgnlv~#9~#M~#J~#F~#B~#0","!#$%(+04:DCSRaonn~#1~#R~#N~#J~#C~#4~#$","!##%(,.5;?DTSZqon~#)~#I~#Q~#N~#C~#4~#%","!##%(*.5;;DOTTsqo}~#A~#U~#R~#C~#4~#%",
  "!##%'*.28;EJUTmsok~#7~#Y~#R~#C~#4~#%","!##%'*.15<FEVUguoj~#$~#N~#R~#C~#4~#%","!##%'+/26<GFWU^uojo~#;~#R~#C~#4~#%","!##%'+/26=GFXUSuojd~#(~#R~#C~#4~#%","!##%')-27=CFQURkojds~#?~#C~#4~#%","!##%'*-27>>FKURbojd`~#,~#C~#4~#%","!##%'*-37><FDURWojd_w~#C~#4~#%","!##%'*-079<FDUROojd_d~#0~#4~#%",
  "!!#%'*-/46<FDUROfjd_X{~#4~#%","!!#%')-/26<FDNRO[jd_Xh~#4~#%","!!#$')+/26<ADHROQjd_XT~#!~#%","!!#%')+/26<<DBROLjd_XRl~#%","!!#%&)+/26<;DBROL`d_XRX~#%","",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 4, 7, 9, 13, 15, 19, 25, 24, 33, 31, 46, 43, 40, 49, 63, 57, 51, 46, 40, 70, 74, 59, 45, 30, 15]
  | 71 => [0, 0, 1, 2, 4, 6, 9, 10, 16, 20, 22, 24, 34, 32, 40, 44, 41, 41, 65, 59, 54, 48, 42, 57, 80, 65, 50, 36, 21, 6]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&(+-265;DBDOLId_XRMJteUG8)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 71).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9729789081440 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8433607719241 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 23 = 2534953173326 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20698349974007 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20698349974007 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9729789081440 exactLoss0
      |>.append 24 8433607719241 exactLoss24
      |>.append 23 2534953173326 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20698349974007,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate22

#print axioms KoalaAt2428Gate22.loss_bound
#print axioms KoalaAt2428Gate22.receipt
