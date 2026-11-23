import ProximityPrize.SubmissionLower.KoalaAt2428Gate28
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate29
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨136,55,8,137,55,3536,4437,⟨9297434221,48215959415,32571097357⟩,4086684261118⟩
abbrev split:ℕ:=48
abbrev unit:ℕ:=1919967678720
abbrev terminal:ℕ:=71
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  b05k,b04t,b040,b037,b033,b022,b010,b00w,
  bzz.take 6++unpack 1 0x19fccbb8,bzv,by2.take 7++unpack 1 0x1affd29c,bxc.take 7++unpack 2 0x48c9d741c035bdf,byj.take 8++unpack 1 0x1c035bdf,bwq,bvs.take 8++unpack 2 0x49cad4020bc9fb1,bv2,
  bvh,btj.take 9++unpack 3 0x4e9bee2494ad44241cef0b,btw,bu3,bsr,bpw.take 9++unpack 5 0x4cd56764e58a6048c9d744c53a062f963280,bqp,bpj,
  bn5.take 10++unpack 7 0x494954849091564d562564ddaaa64a0a5504a4e9d8319c975b,bll.take 10++unpack 8 0x25060c024848ab3f4f1ceba4cd4646498ad664bd322235a94400,blk.take 11++unpack 7 0x24848ab3f4b4fdce4f1cebc4b0f5dc490ad6a31f3158c,bkr,bl6,bj9,bie.take 11++unpack 9 0x4a0c582494994a494a1284cd5a624f1bec44a4d1a6494a9404d172923f1c6af1,bgg,
  bgy,bbb.take 12++unpack 10 0x272df6924a50942484aab24848b1268b315278e16c25276ea234c52df84179141f,bdg.take 13++unpack 9 0x25e972624846b524848b12484aa0278e75c272d96f234a0b5283e6f7cd3,bdt.take 14++unpack 8 0x242491624438dc2484aa025a88de27adf6c262b329693e6f7cd3,b7c,b4t.take 13++unpack 10 0x2d45d11f448861fa484899a4f9e2624f9f620494961649085d64c531fa4838d99e,b83.take 14++unpack 9 0x2d4c52dfe4349dfa4acedfa50606065415220430c6084847206452f33dc,b8h,
  b4z.take 14++unpack 9 0x2d2694a33cc9e2b4544c9ad44129f64cf281dc,b4l,b4m,b4n,b4o,b4p,b4q,b4r,
  b58,b5m,b5l,b69,b4b.take 23,[]]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 17 then [] else boxesTape.getD (r-17) []

def plain : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "","!#","!#&","!#&+","!#&+",z3r,z2Q,z4F,
  "!#%(-8>",z41,z5l,z3q,"!#%(+3<CJ","!#%(,4==LN","!#$',08=ML","!#$'-05>OM_",
  z68,z4M,z3y,z3x,"!#$&*.48BOUVw","!#$&*.28CIWUo~#&",z3o,z6D,
  z5z,z3K,z3u,z31,"!#$&(-15=JIZa_v~#9~#5~#1~#-","!#$%(+16=EJTcan~#1~#9~#5~#1~##",z3k,"!#$%),27?>LKgec~!~~#A~#=~#9~#5~##",
  "!!#%(,/7;?ML`geu~#9~#A~#=~#9~#/","!!#%(,.47@NMZigm~#0~#E~#A~#=~#9~##","!!#%(*/28@INSkig~#(~#H~#E~#A~#=~#/","!!#%(*/38ADONlki}~#@~#H~#E~#A~#;","!!#%'+/39BAPOflku~#8~#L~#H~#D~#?~#/","!!#%'+039BBRP`nll~#0~#P~#L~#H~#?~#1","!!#%'+-4:>BSRYpnl~#(~#H~#P~#L~#?~#1","!!#%')-4::CNSSrpmx~#@~#T~#M~#?~#1",
  "!!#%'*-17:DITSlrmg~#1~#X~#M~#?~#1","!!#%'*.05;EDUSdrmg|~#H~#M~#?~#1","!!#%'*.15;EDVSYrmgj~#6~#M~#?~#1","!!#%'*.15<FDVSPrmgb~#$~#M~#?~#1","!!#$&),16<ADOSPhmgbn~#:~#?~#1","!!#$&),26<<DHSP_mgb]~#(~#?~#1","!!#$&),26<;DCSPTmgb]s~#?~#1","!!#$'),/68;DCSPMmgb]a~#-~#1",
  "!!#$&),.25;DCSPMcgb]Vx~#1","!!#$&(,.15;DCLPMXgb]Ve~#1","!!#$&(*.15;?CEPMOgb]VR|","!!#$&(*.15;:CAPMJgb]VQj","!!#$&(*.15;:CAPMJ^b]VQW",""]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

private def plainPowers : ℕ → List ℕ
  | 70 => [0, 0, 1, 2, 3, 6, 8, 12, 15, 18, 24, 23, 32, 30, 45, 42, 39, 47, 61, 55, 50, 45, 40, 70, 74, 61, 47, 33, 20]
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!!#$&'*,157:CAIMJJb]WQL]tfWJ<."

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 70).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private abbrev Chunk (i n v : ℕ) := lossChunk 12 envelope plain boxes i n = v
private theorem checkPart (i n v : ℕ) (ok : Chunk i n v := by decide +kernel) : Chunk i n v := ok
private def part0 := checkPart 0 6 0x2384dc4cc14
private def part1 := checkPart 6 6 0x2384dc4cc14
private def part2 := checkPart 12 6 0x237ddef64bb
private def part3 := checkPart 18 6 0x231febf640d
private def part4 := checkPart 24 6 0x224ce6a60f7
private def part5 := checkPart 30 6 0x20bf5579c40
private def part6 := checkPart 36 6 0x1e06eed3176
private def part7 := checkPart 42 6 0x19bbad3fb06
private def part8 := checkPart 48 6 0x1372498b968
private def part9 := checkPart 54 6 0xbb80806c06
private def part10 := checkPart 60 6 0x58fd82eee5
private def part11 := checkPart 66 4 0x1b7c2baf86

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20815634714236 N :=
  loss_of_chunks 12 envelope terminal plain boxes 20815634714236 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 6 0x2384dc4cc14 part0 |>.append 6 0x2384dc4cc14 part1 |>.append 6 0x237ddef64bb part2 |>.append 6 0x231febf640d part3
      |>.append 6 0x224ce6a60f7 part4 |>.append 6 0x20bf5579c40 part5 |>.append 6 0x1e06eed3176 part6 |>.append 6 0x19bbad3fb06 part7
      |>.append 6 0x1372498b968 part8 |>.append 6 0xbb80806c06 part9 |>.append 6 0x58fd82eee5 part10 |>.append 4 0x1b7c2baf86 part11)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20815634714236,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate29

#print axioms KoalaAt2428Gate29.loss_bound
#print axioms KoalaAt2428Gate29.receipt
