import ProximityPrize.SubmissionLower.CL
import ProximityPrize.SubmissionLower.CP
set_option Elab.async false
open _root_ renaming Code.closeCodewordsRel→ oq,Finset→mD,Finset.card_image_of_injective→ oj,Finset.range→lJ,Fintype.card→n5,IsCoprime→lV,Nat.add→cy,Nat.div→nI,Nat.land→nX,Nat.mul→lI,Nat.shiftRight→nq,Nat.sub→c9
set_option autoImplicit true
section
namespace acY.Compact
set_option maxHeartbeats 2000000
open xE GI abF
open private Cc afE EH Cd aDb from ProximityPrize.SubmissionLower.CM
open private beR bDz balance from ProximityPrize.SubmissionLower.CK
open private rowStart Sk IK Eu E0 from ProximityPrize.SubmissionLower.CL
open private strict iW ajv boX aaj agY Zb am7 ab0 from ProximityPrize.SubmissionLower.BR
private def bZG (d l c o:ℤ) (j:ℕ) :ℕ :=
 let r :=(min d ((o-1-l+d)/4)+1).toNat
 Yp d.toNat (l.toNat-j) (3*c+1).toNat (o.toNat-j) r
private theorem cJq (d l c o:ℤ) (j:ℕ)
  (hd:0≤d) (hc:0≤ c) (hl:l-j-1≤3*c) (hb:0≤o-1-l+d) :
  bZG d l c o j=(Cd d (l-j) c (o-j)).toNat := by
 let F:Flag:=⟨d,l-j,3*c,c,o-j⟩
 let r :=(min d ((o-1-l+d)/4)+1).toNat
 change Yp d.toNat (l.toNat-j) (3*c+1).toNat (o.toNat-j) r= _
 rw [aDb]
 have hl' : l.toNat-j=(l-j).toNat := by omega
 have ho' : o.toNat-j=(o-j).toNat := by omega
 rw [hl',ho']
 have hbal:balance F=o-1-l+d:= by dsimp only [balance,F]; ring
 have hrpos :0≤ min d ((o-1-l+d)/4)+1 := by
  have :0≤(o-1-l+d)/4 := by omega
  omega
 exact beR F d.toNat (3*c+1).toNat r (by dsimp [F]; omega)
  (by dsimp [F]; omega) (by dsimp [F]; omega) hc le_rfl hl (by rw [hbal]; exact hb)
  (by rw [hbal]; exact Int.toNat_of_nonneg hrpos)
private theorem dUf (old ini res :ℤ) :
 (old - max 0 ini).toNat - (old - max (max 0 ini) res).toNat =
   (old.toNat - ini.toNat)-(old.toNat - res.toNat) := by omega
private def bc2 (j:ℕ) :ℕ:=125576826-ajv (1650-j)
private theorem dT8 (j:ℕ) :bc2 j=(EH 1650 (1650-j) 550).toNat := by
 unfold EH
 rw [min_eq_right (show (1650:ℤ)-j-1≤3*550 by omega)]
 change _=((125576826:ℤ) - Cc 1650 (1650-j-1)).toNat
 have he : (ajv (1650-j) :ℤ)=Cc 1650 (1650-j-1) := by
  rw [afE]
  change _=gd ((1650:ℕ) :ℤ) ((1650:ℤ)-j-1)
  rw [← bDz 1650 (1650-j),← boX]
  have ht: ((1650:ℤ)-j).toNat=1650-j:= by omega
  rw [ht,JY,ite_eq_left (by omega)]
 rw [← he]
 unfold bc2
 omega
private def cJs (d l c o:ℤ) (j:ℕ) :Bool :=
 decide (0≤d∧0≤ c∧l-j-1≤3*c∧0≤o-1-l+d)
private def cJn (s :ℕ) (d l c o:ℤ) (j:ℕ) :ℕ :=
 let old:=bc2 j
 (old - bZG 1650 1650 550 (4650-s) j)-(old - bZG d l c o j)
private theorem dT6 (s j start:ℕ) (p:kJ) (hj:start≤j)
   (hs :s≤4649)
   (hg:cJs (1650-(p.value+(p.top:ℤ)+3*p.Ej)) (1650-(3*(p.top:ℤ)+2*p.Ej))
     (550-(p.top+(p.Ej:ℤ))) (4650-s-(2*(p.top:ℤ)+3*p.Ej)) start=true) :
   cJn s (1650-(p.value+(p.top:ℤ)+3*p.Ej)) (1650-(3*(p.top:ℤ)+2*p.Ej))
     (550-(p.top+(p.Ej:ℤ))) (4650-s-(2*(p.top:ℤ)+3*p.Ej)) j=Zr s j p:= by
 obtain ⟨hd,hc,hl,hb⟩:=of_decide_eq_true hg
 unfold Zr cJn
 rw [dUf,dT8,cJq _ _ _ _ _ hd hc (by omega) hb,
   cJq _ _ _ _ _ (by decide) (by decide) (by omega) (by omega)]
 rw [show (1650:ℤ)-(3*(p.top:ℤ)+2*p.Ej) - j=1650-j-(3*(p.top:ℤ)+2*p.Ej) by ring,
   show (4650:ℤ) - s-(2*(p.top:ℤ)+3*p.Ej) - j=4650-s-j-(2*(p.top:ℤ)+3*p.Ej) by ring]
private def ag0 (d l u o r :Nat) :Nat :=
 c9 (cy (aaj d u) (Zb d (c9 o (lI 3 r)) r))
  (cy (aaj d o) (Zb d l r))
private theorem k_eq (d l u o r :Nat) :Yp d l u o r=ag0 d l u o r := by
 simp only [Yp,ag0,agY,am7]
 rfl
private def ahf (s :Nat) (f :Nat→Nat) :Nat→Nat
 | 0=>0
 | n+1=>Nat.add (ahf s f n) (f (Nat.add s n))
private theorem ejf (s :Nat) (f :Nat→Nat) (n:Nat) :
   ahf s f n=Eu f s n:= by
 induction n with
 | zero=>rfl
 | succ n ih=>rw [ahf,Eu,ih]; rfl
private def atG (s j n a b c:Nat) :Nat :=
 strict (c9 1650 (cy (cy a b) (lI 3 c))) fun d =>
 strict (c9 1650 (cy (lI 3 b) (lI 2 c))) fun l =>
 strict (c9 1651 (lI 3 (cy b c))) fun u =>
 strict (c9 4650 (cy (cy s (lI 2 b)) (lI 3 c))) fun o =>
 strict (cy (c9 d (c9 d (nI (c9 4649 (cy (cy s a) (lI 4 c))) 4))) 1) fun r =>
 strict (c9 4650 s) fun o₀ =>
 strict (cy (nI (c9 4649 s) 4) 1) fun r₀ =>
  ahf j (fun k=>strict k fun k =>
   let old:=bc2 k
   let ini:=ag0 1650 (c9 1650 k) 1651 (c9 o₀ k) r₀
   let res :=ag0 d (c9 l k) u (c9 o k) r
   c9 (c9 old ini) (c9 old res)) n
private theorem fbS (s j n a b c:Nat) (hs :s+a+4*c≤4649)
    (hh:a+b+3*c≤1650) (hc:b+c≤550) (hj:c≤j+1) :
    atG s j n a b c=Eu (fun k=>Zr s k ⟨a,b,c⟩) j n:= by
  simp only [atG,iW,ejf,ab0,← k_eq]
  let d:ℤ:=1650-(a+(b:ℤ)+3*c)
  let l:ℤ:=1650-(3*(b:ℤ)+2*c)
  let cap:ℤ:=550-(b+(c:ℤ))
  let o:ℤ:=4650-s-(2*(b:ℤ)+3*c)
  have hg:cJs d l cap o j=true := by
    apply decide_eq_true
    dsimp [cJs,d,l,cap,o]
    omega
  have hd:d.toNat=1650-(a+b+3*c) := by dsimp [d]; omega
  have hl:l.toNat=1650-(3*b+2*c) := by dsimp [l]; omega
  have hu: (3*cap+1).toNat=1651-3*(b+c) := by dsimp [cap]; omega
  have ho:o.toNat=4650-(s+2*b+3*c) := by dsimp [o]; omega
  have hb:o-1-l+d=4649-(s+(a:ℤ)+4*c) := by dsimp [o,l,d]; ring
  have hq: (min d ((o-1-l+d)/4)+1).toNat =
      min (1650-(a+b+3*c)) ((4649-(s+a+4*c))/4)+1 := by
    rw [hb]
    omega
  have hq₀: (min (1650:ℤ) (((4650-(s:ℤ))-1-1650+1650)/4)+1).toNat=(4649-s)/4+1 := by omega
  have ho₀: (4650-(s:ℤ)).toNat=4650-s := by omega
  have hh' (k :Nat) (hk :j≤k) :cJn s d l cap o k=Zr s k ⟨a,b,c⟩ :=
    dT6 s k j ⟨a,b,c⟩ hk (by omega) hg
  have hnat (k :Nat) :cJn s d l cap o k =
      (bc2 k-Yp 1650 (1650-k) 1651 (4650-s-k) ((4649-s)/4+1)) -
      (bc2 k-Yp (1650-(a+b+3*c)) (1650-(3*b+2*c)-k) (1651-3*(b+c)) (4650-(s+2*b+3*c)-k)
        (min (1650-(a+b+3*c)) ((4649-(s+a+4*c))/4)+1)) := by
    simp only [cJn,bZG,hq,hq₀,hd,hl,hu,ho,ho₀]
    rfl
  induction n with
  | zero=>rfl
  | succ k ih =>
    rw [Eu,Eu,ih,← hh' (j+k) (by omega),hnat (j+k)]
    rfl
private def atF (s j code :Nat) :Nat :=
 bif Nat.beq (Nat.mod code 2147483648) 0 then 0 else
 strict (Nat.mod code 2048) fun a =>
 strict (Nat.mod (nI code 2048) 1024) fun b =>
 strict (Nat.mod (nI code 2097152) 1024) fun c =>
 strict (cy (nI code 2147483648) 1) fun n =>
   bif Nat.ble (cy (cy s a) (lI 4 c)) 4649 &&
     Nat.ble (cy (cy a b) (lI 3 c)) 1650 &&
     Nat.ble (cy b c) 550 && Nat.ble c (cy j 1)
   then atG s j n a b c else IK s j code
private theorem fbR (s j code :Nat) :atF s j code=IK s j code := by
 simp only [atF,iW,Bool.cond_eq_ite,Nat.beq_eq,Nat.ble_eq,Bool.and_eq_true]
 split
 · rename_i h
   have h' : code % 2147483648=0:=h
   simp only [IK,h',ite_true]
 split
 · rename_i hz h
   unfold IK
   have hz' : ¬ code % 2147483648=0:=hz
   rw [ite_eq_right hz']
   exact fbS s j _ _ _ _ h.1.1.1 h.1.1.2 h.1.2 h.2
 · rfl
private def abN (s :Nat) :Nat→List Nat→Nat
 | _,[]=>0
 | j,code :: more =>
   strict code fun code=>strict j fun j =>
     cy (atF s j code) (abN s (cy j (cy (nI code 2147483648) 1)) more)
private theorem fbN (s j:Nat) (xs :List Nat) :abN s j xs=Sk s j xs := by
 induction xs generalizing j with
 | nil=>rfl
 | cons k xs ih=>simp only [abN,iW,fbR,ih,Sk,E0]; rfl
def aeV:Nat→List (List Nat)→Nat
 | _,[]=>0
 | s,xs :: more=>Nat.add (abN s (rowStart s) xs) (aeV (Nat.add s 1) more)
theorem djo (s :Nat) (xs :List (List Nat)) :aeV s xs=value s xs := by
 induction xs generalizing s with
 | nil=>rfl
 | cons x xs ih=>simp only [aeV,value,ih,fbN]; rfl
theorem join {s n m v w:Nat} {a b:List (List Nat)}
  (ha :a.length=n∧fits s a=true∧value s a=v)
  (hb:b.length=m∧fits (s+n) b=true∧value (s+n) b=w) :
  (a ++ b).length=n+m∧fits s (a ++ b)=true∧value s (a ++ b)=v+w:= by
 simp only [List.length_append,aUX,a9s,ha.1,hb.1,ha.2.1,hb.2.1,
  Bool.true_and,ha.2.2,hb.2.2,and_self]
private def fcN :Nat :=0x4004010000001020000000410000000101000000040c00008000040c0c00100c001000403000000100c002000002600400000980080000240000000090010000023000000008c05000803001000200c0038008030002002600003000803000800200c000000900000400200c000000803000c001806000818400000e000c0400103000100000006030010301800006180800001800000c002100600001800603000600000a000800603001000100c003800403000a00100c001800403000200100c00280000260020000098000000026008000009001800002400400000900080000220000000088000000021800003060005000c03000e00300c004800803000a00300c002800803000400300c001000001b000000006c00000001a0000000066000028000002001808000000001400004100000001830000000000036010302000008200c00001030000c00a000c0c0008010040000004010000000004031600100c005000403001200100c00100100000000018080018000026002000008c04800c03001000300c003000c030000002300001000980000800300c001800c03000200300c000000c030000000007000800001b00200000683480000000000c30000298000000088000000002000602000400180801f800000007a00000001d00000000000118000190000000004000004c00800001305e0000000000000012052000000000000001184a0000000018c0800004000000000f000000003600000000b00000000280000000098000000022000000007000000001800000000480000000000800040040c06000000080800000030000c0000c0004002800000000c000003002800000c002060003002000000c00001000300003018000041808000030c04000008000c0c003801000003200300c00000000401140000100048000040002004000000000002800c0000100020000040002030010000000004001c00000800600000200140000080040000020002003400005800c03000a0000080000009800006000008001000002000000000803b80000000ec00000003a80000000e800000003900000000e200000003780000000dc0000000368000000000001006032000000000010300002f00000000b400000002c00000000ae00000002b000000000c00000602a80000000a80000000290000000008000006028000000009e000000027000000009a000000026000000000400000600080000180940000000248000000090000000023800000008a00000002180000000060018080000308000084000000020800000008000000001e000000007200000001c000000006e00000001b000000006a00000001a00000000020618000188000000000000004c1680000000020000048160000000056000000014000000004e00000001300000000480000000118000000044000000010800000003a00000000d000000003200000000c000000002e000000000000001001e0000000050000000000000183000000080c00e0000000018c0400000600000000080000000000080030000401800006200c00001000603001c00001000180030300000000104010003030002000c0c000000303001000001000380000400000040000028000040006000010000800004000e000008003000002001a00200803980000000e000000003600000000d6000000035000000000200080803400000000ce00000000000020200cc00000003280000000c600000003100000000c2000000030000000001800000602f800000001600000602e800000001400000602e0000000012000006002000802001000000602c800000000e0000060288000000000001c00023000000007c00000000084080000760000000000408000004182000019800000000218200000006080000600000000170000000054000000003000001003e000000002800001000020100000e0000000008000004001800001000400000400a80000000240000000080000000002180c000068000000016000000000000101000010080000400000000021008000030000000002200c00002000000000018080000100000000001000030008602000000018003000000000000000180c0070004030016000010006000403000800400000180100000040000100068000020016000008007000c030012000008006800c03001800300c00580080300080000080008000020000000408001000202001a00000602d800000000a000006001800001809600000000000000180000006060000c060000043018000018c060000040c100000088040000042010000008000010000180c000000c0400000430100000008030000001000040020c04000004200c000068000040000000010086000004000a00400000b800803002400300c008800c03002000300c007800c03001a00200c0060008030000000608002060c000006002008001000802000200200800000080200000120000000066000000000406004000301801000100600200040180060010060008c0600000200100600103030000023010000008300010006100800000008000c00a3010000010603000002100003000000004042a00300c00a000c03002600300c0098006020010001008000840c00000a002008002800602000a0018060050004018012001006003800401800c0010060028004018004001006000018400000c000c0400000000900000c0c0000083018000062010000020c0600000000001018b000c0300180030000010003020002000608000006800000200060600580040180001018000008606000002101000003000002602e00300c000800302000206200000084060000020810000020003010000000c04000000019000010100000188060000041810000000806000000080003002080400002600200c008000803001c00200c005800c000002001008003000602000800180600180060180000018060000306000000202000000000301800a000c040018003010004000c04000800301000000004400082030000082018000008806000006100c0000086040000001810000008403000000100c0000000c000c000000010208800803001e00200c004800c000010003000003800c000008003000000000302000a0010080020004020004001008005800602001000180800100060180020018060010808000002202000001060600000018180000108060000020800030000000040c0c0040000090008030014003000003800402000c0010080018004020000021800003800301800c000c060008003018000081000000030400000000080400206030000020c0003000000c20000c003000002800c000004003000005000602000620200000200030180000c08000028c0600000000c00000b000803002a00200c00a0008030006003000000000c000018001808004800602000e0018080010306000004000c0600280020100020c0800001040200001a00100c0008000028000014000004000802000c002008007800602001a0018080000000210006180c000028003020002003000000000402001c001808001030800000a000c060018003018006000804001000201000001c0000000000120000000028004800802000e00200800000001980000000460020002010002000804000818c000000022000008000602000000002600000c600000a201000000010000c002060010000000830000600080600002060000061010000028806000008181000000018000c00000000810000001a0008202000000020300000000000804000000202000000080c00000c20000002800000060c00001a001006003080400000000b00000080086000061018000038c0600000200060400000900000000130000018002020002000806001040300000400000a00000020180021830000000000310002000204000800c600000000088000006c0000000820000030c06000000003200000020c0000003020000010008c0000000008600184080000020c10000000000c1000003200000001060000020400100000000c18006181000002880800000003400000000200400000180100020606000004302000000830300003000300c000019000000418300000000400400020002080010404000006000c080000008800002000206000820600000230200000000003180061818000038000026002000408000008c0000220018080000186000000060010000000032000600240000080000210040c3000003080600000000000840000000208020820000020608000000000104000000002060800260000280020200061830000050008020000042000001000101000000360000000018100000030c000001000400180020080010002018002000406000018800000c202000001000cc000020c1800001800d0000000440000058008020004101800001840c00000002001000000cc000004102000006000401800200040400083080000000001080028000024000000204000000001840000000604000000182000000060c0000082000600260000186080000000001840010009000000000106001000182001c000006001040c0000240018080018001818006000008c008000c10004003400001800182000000020600000c0040004000008800830c0000020033000008008c00002000008600820c0000000021000010001818002002200000018c0000000000083000000620004000408000010c00001e000008000000061800200030800100010180020000050008000c180020032000020003020008000808000000c600000002180000000001040000000404000000102000000040c40000010004000007000800001c000003100000800000e002000006400000000c2000000030c4000000c000000003100000001900000000304000000188000000000c00000002300000000cc000000043000000018c00000008302000002800000000040000000090000000034000000011000000006400000002100000001860000000004000000011000000006400000002100000000c400000004100000001840000000810000000008000000012000000006800000002200000000c800000004200000001880000000821e00000600080000110000000044000000010800000004181800001b0040000068008000019802000003400000000d000000003200000000c60000000630000000008020000006008000002004000000c0100000040000000012020000006000000001a020000008000000002200000000900000000018000000018000000008000000002602000000c0000000036020000010000000004600000001401800000600000000198000000070060000020000000008602000002401000001400e000004000000000e00e000003001800001300000000280100000120020000046000000010c02000003600000000cc0000000030000000010000000013000000006c0000000230080000098
private def codes :Nat→Nat→List Nat
 | 0,_=>[]
 | n+1,stream =>
   strict stream fun stream =>
   let long:=nX stream 1
   let index :=nX (nq stream 1) (bif Nat.beq long 0 then 127 else 1023)
   let rest:=nq stream (bif Nat.beq long 0 then 8 else 11)
   nX (nq fcN (lI 38 index)) 274877906943 ::
     codes n rest
private def rows :Nat→Nat→List (List Nat)
 | 0,_=>[]
 | n+1,stream =>
   strict stream fun stream =>
   let count:=nX stream 255
   let width :=nX (nq stream 8) 2047
   let payload :=nq stream 19
   codes count (nX payload (c9 (Nat.shiftLeft 1 width) 1)) ::
     rows n (nq payload width)
private theorem fbQ (n data :Nat) : (rows n data).length=n:= by
 induction n generalizing data with
 | zero=>rfl
 | succ n ih=>simp only [rows,iW,List.length_cons,ih]
structure Chunk (s n t:Nat) where
 data :List (List Nat)
 len:data.length=n
 Ay :fits s data=true
 score :value s data=t
def cert (s n t data :Nat) (h:fits s (rows n data)=true) (v :aeV s (rows n data)=t) :Chunk s n t :=
 ⟨rows n data,fbQ n data,h,(djo s _).symm.trans v⟩
def add {s m n x y :Nat} (l:Chunk s m x) (r :Chunk (s+m) n y) :Chunk s (m+n) (x+y) :=
 let h:=join (a :=l.data) (b:=r.data) ⟨l.len,l.Ay,l.score⟩ ⟨r.len,r.Ay,r.score⟩
 ⟨l.data ++ r.data,h.1,h.2.1,h.2.2⟩
end acY.Compact
end
section
namespace ju
inductive Bank where
 | leftLow | rightLow | leftHigh | rightHigh
 deriving DecidableEq
structure Block where
 aV:Bank
 cap:Nat
 free :List (Nat×Nat)
 y6:List (List (List Nat))
def Block.coeff (z :Block) (j i k :Nat) :Nat :=(((z.y6[j]?).getD [])[i]?.getD [])[k]?.getD 0
end ju
end
section
namespace ju
def total {α:Type*} [AddMonoid α] (f :ℕ→α) :ℕ→α
 | 0=>0
 | n+1=>total f n+f n
def n9 (n k :ℕ) :=n.descFactorial k/k.factorial
end ju
end
section
namespace ju
open scoped BigOperators

theorem abt {α:Type*} [AddCommMonoid α] (f :ℕ→α) (n:ℕ) :
   total f n = ∑ i∈lJ n,f i:= by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [total,Finset.sum_range_succ,ih]
theorem cfv {F ρ κ:Type*} [Field F] [Fintype ρ] [Fintype κ]
  (M:Matrix ρ κ F) {d:ℕ} (V:Matrix κ (Fin d) F) (free :Fin d→κ)
  (hMV:M*V=0) (hid :V.submatrix free id = 1) :
  M.rank+d≤n5 κ:= by
 have h:=V.rank_submatrix_le free id
 rw [hid,Matrix.rank_one,Fintype.card_fin] at h
 exact (Nat.add_le_add_left h _).trans (Matrix.rank_add_rank_le_card_of_mul_eq_zero hMV)
end ju
end
section
namespace i4
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem ProximityPrize.Benchmark
open yP.baR (YP R16 aP2 awE flatten b3y
 b3D b3x)
open yP.a92
open scoped NNReal
theorem glZ {A cap} (hlist:axW A cap) (w:Node→K) (P:mD (Node→K))
    (hP : ∀ f∈P,f∈aP2∧A≤aaC f w) :P.card≤ cap:= by
  classical
  have :NeZero (k :ℕ) :=⟨by decide⟩
  choose poly hdegree heval using fun f :P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj:Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i=(poly f).eval (IRSProfile.domain i) :=(heval f i).symm
      _=(poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _=g.val i:=heval g i
  let polys :mD K[X] :=Finset.univ.image poly
  have hpolyscard:polys.card=P.card:= by
    dsimp [polys]
    rw [oj _ hinj]
    simp
  have hpolys : (polys :Set K[X]) ⊆
      close A w:= by
    intro q hq
    obtain ⟨f,_hf,rfl⟩:=Finset.mem_image.mp hq
    refine ⟨?_,?_⟩
    · have hd: (poly f).natDegree<k :=hdegree f
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · refine (hP f.val f.property).2.trans (Finset.card_le_card ?_)
      intro i hi
      apply (ReedSolomon.mem_polynomialAgreementSet node w (poly f) i).mpr
      have hfw:f.val i=w i:= by
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      exact (heval f i).trans hfw
  obtain ⟨hfinite,hbound⟩:=hlist w
  have hcount:=(Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card≤ cap:= by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'
theorem guv {A cap} (hlist:axW A cap)
    (hroom: (cap+1)^2≤n5 K) (w:Node→YP) (P:mD (Node→YP))
    (hP : ∀ f∈P,f∈awE∧A≤aaC f w) :P.card≤ cap:= by
  classical
  let flattened:=P.image flatten
  have hflat : ∀ f∈flattened,
      (∀ r :R16,(fun i ↦ f i r)∈aP2) ∧
        A≤aaC f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩:=Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩:=hP g hg
    exact ⟨b3D g hcode,hagree.trans (b3x g w)⟩
  have hcount:=cSg aP2 A cap hroom
    (glZ hlist) (flatten w) flattened hflat
  have hcard:flattened.card=P.card:=oj P b3y
  rwa [hcard] at hcount
theorem bwW {A cap} (hlist:axW A cap)
    (hroom: (cap+1)^2≤n5 K) (radius :ℝ)
    (hcut : ∀ f w:Node→YP,(δᵣ(w,f) :ℝ)≤ radius→A≤aaC f w) :
    Code.Lambda (awE :Set (Node→YP)) radius≤(cap:ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (oq (awE :Set (Node→YP)) w radius).Finite :=
    Set.toFinite _
  have hcard:hfinite.toFinset.card≤ cap:= by
    apply guv hlist hroom w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩:=Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,hcut f w hclose⟩
  calc
    (oq (awE :Set (Node→YP)) w radius).encard =
        (hfinite.toFinset.card:ℕ∞) :=hfinite.encard_eq_coe_toFinset_card
    _≤(cap:ℕ∞) := by exact_mod_cast hcard
end
end i4
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I e9 node p blockLength k kB nC aB8 ayo
 sZ aiE vn seed jH twist uO Ox Xb
 JO J9 Z4 ake)
structure a08 where
 dw:ℕ
 numerator :ℕ
 denominator :ℕ
 aou:ℕ
 mcaBound:ℕ
 listBound:ℕ
abbrev target :a08:=⟨179944,336691697,1073741824,2369,0x3aca17061ce8c43,8491707658716571⟩
abbrev dw:=target.dw
abbrev radiusNumerator :=target.numerator
abbrev radiusDenominator :=target.denominator
abbrev ajO:ℤ:=target.aou
abbrev t:ℕ:=blockLength - dw
abbrev L:ℕ:=dw - k
abbrev DY:ℕ:=t+1 - L - 2
abbrev budget:ℕ:=0x3d0ed83eb28710f
def Xt:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
def radius :ℝ:=Xt
def Tt (u:e9) (Γ:mD K) :Prop :=
 ∀ γ∈Γ,IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
structure a9J (A:ℕ) (u:e9) (γ:K) where
 support :mD I
 decoder :K[X]
 dw:A≤ support.card
 degree :decoder.degree<k
 lg : ∀ i∈support,decoder.eval (node i)=u 0 i+γ*u 1 i
 nonjoint : ¬ (NM node (u 0) k support∧NM node (u 1) k support)
abbrev B5:=a9J dw
def iy (u:e9) := QO node (u 0) (u 1) L t
def So (u:e9) :=AI p node (u 0) (u 1) L t
def Vv (u:e9) :=Bx.adJ (So u)
def R5 (u:e9) :=Bx.ay6 (So u)
def Normal (u:e9) (γ:K) :Prop :=
 ((So u).map (evalRingHom γ)).rank=Vv u
structure qo (u:e9) where
 a :ℕ
 b:ℕ
 c:ℕ
 ab:a≤b
 active :b≤t
 inactive :t<c
 top:c≤k
 degreeSum:a+b+c=2*k+2
 nullitySum:R5 u+a+b=2*(t+1)
 level :kL.aKl
   (fun s j=>algebraMap K[X] kB (Principal.P8 p node (u 0) (u 1) s j))
   k a b c
def qo.height {u:e9} (T:qo u) :=(k+1) - T.c
abbrev Relation {u:e9} (T:qo u) :=
 kL.axT p node (u 0) (u 1) k T.height
def y1 {u:e9} {T:qo u} (R:Relation T) :nC :=
 Principal.assemble (fun j=>R.coefficients (0,j))
def zv {u:e9} {T:qo u} (R:Relation T) :nC :=
 Principal.assemble (fun j=>R.coefficients (1,j))
def pJ {u:e9} {T:qo u} (R:Relation T) :mD I:= by
  classical
  exact Finset.univ.filter fun i =>
    (y1 R).eval (C (node i))=0∧(zv R).eval (C (node i))=0
structure Reduction (u:e9) (T:qo u) (R:Relation T) where
 U:nC
 V:nC
 output :nC
 height:ℕ
 height_eq :height+(pJ R).card=T.height
 max_degree :max U.natDegree V.natDegree=height
 U_ne :U≠0
 V_ne :V≠0
 coprime :lV (sZ U) (sZ V)
 U_factor :y1 R=jH (mL node (pJ R))*U
 V_factor :zv R=jH (mL node (pJ R))*V
 output_factor :R.output=jH (mL node (pJ R))*output
 output_degree :output.degree<(k+height:ℕ)
 deleted_error : ∀ γ,Normal u γ → ∀ M:B5 u γ,∀ i∈pJ R,
   M.decoder.eval (node i)≠u 0 i+γ*u 1 i
structure KJ (u:e9) (T:qo u) (R:Relation T)
   (D:Reduction u T R) where
 rank_eq :Xb D.U D.V=3
 α:Fin 2→K[X]
 β:Fin 2→K[X]
 a :K[X]
 b:K[X]
 a_ne :a≠0
 b_ne :b≠0
 α_primitive :lV (α 0) (α 1)
 β_primitive :lV (β 0) (β 1)
 first_degree :a.natDegree+uO (β 0) (β 1)≤D.height
 second_degree :b.natDegree+uO (α 0) (α 1)≤D.height
 same_direction :Z4 D.U D.V (JO a β) (J9 b α)
 output :nC
 output_degree :output.degree<(k+D.height:ℕ)
 nodes :ake u (pJ R) (JO a β) (J9 b α) output
structure FJ (maxHeight:ℕ) (u:e9) (deleted:mD I) where
 shift:K
 pencil₀:K[X]
 pencil₁:K[X]
 pencil₀_degree :pencil₀.degree<k
 pencil₁_degree :pencil₁.degree<k
 E :K[X]
 factor :K[X]
 Q:K[X]
 A₀:K[X]
 A₁:K[X]
 word:I→K
 word_fixed : ∀ i,twist (word i)=word i
 word_deleted : ∀ i∈deleted,word i=0
 E_monic:E.Monic
 aFF : ∀ i,E.eval (node i)≠0
 factor_nodes : ∀ i∉deleted,factor.eval (node i)≠0
 coprime_factor :lV E factor
 offset_proper :Q.degree<E.degree
 offset_reduced:lV Q E
 adjacent_coprime :lV E (E.map twist)
 amplitudes_primitive :lV A₀ A₁
 first_amplitude_unit :lV A₀ E
 aVi:E.natDegree+uO A₀ A₁≤ maxHeight
 first_word : ∀ i∉deleted,
   E.eval (node i)*(u 0 i+shift*u 1 i - pencil₀.eval (node i)) =
     factor.eval (node i)*A₀.eval (node i)*word i
 second_word : ∀ i∉deleted,
   E.eval (node i)*(u 1 i - pencil₁.eval (node i)) =
     Q.eval (node i)+factor.eval (node i)*A₁.eval (node i)*word i
def FJ.iF {h u deleted} (M:FJ h u deleted) :ℤ :=
 (M.E.natDegree :ℤ)-M.factor.natDegree - uO M.A₀ M.A₁
def FJ.label {h u deleted} (M:FJ h u deleted) (γ:K) :K :=
 γ-M.shift
def FJ.wK {h u deleted} (M:FJ h u deleted) (γ:K) :K[X] :=
 M.A₀+Polynomial.C (M.label γ)*M.A₁
def FJ.decoder {h u deleted} (M:FJ h u deleted) {A:ℕ} {γ:K}
    (B:a9J A u γ) :K[X] :=
  B.decoder-M.pencil₀-Polynomial.C (M.label γ)*M.pencil₁
structure bjQ {A h:ℕ} {u deleted} (M:FJ h u deleted) (γ:K) (S:K[X]) where
 bad:a9J A u γ
 avoids_deleted:Disjoint bad.support deleted
 scalar_fixed:S.map twist=S
 aic:S=0∨(S.natDegree :ℤ)≤(k :ℤ) - 1+M.iF
 scalar_hits : ∀ i∈bad.support,S.eval (node i)=M.word i
 pole_unit :lV (M.wK γ) M.E
 identity :M.E*M.decoder bad-Polynomial.C (M.label γ)*M.Q =
  M.factor*M.wK γ*S
structure bje (A:ℕ) {h:ℕ} {u deleted} (M:FJ h u deleted) (Γ:mD K) where
 scalar :K→K[X]
 mark : ∀ γ∈Γ,bjQ (A:=A) M γ (scalar γ)
 distinct :Set.InjOn scalar (Γ:Set K)
abbrev jG:=FJ DY
abbrev mJ {u deleted} (M:jG u deleted) :=bje dw M
abbrev jG.iF {u deleted} (M:jG u deleted) :=FJ.iF M
abbrev jG.label {u deleted} (M:jG u deleted) :=FJ.label M
abbrev jG.wK {u deleted} (M:jG u deleted) :=FJ.wK M
abbrev jG.decoder {u deleted} (M:jG u deleted) {γ:K} (B:B5 u γ) :=
 FJ.decoder M B
structure aYT where
 lo:ℕ
 hi:ℕ
 prefixFee :ℕ
 Z1 :ℕ
inductive gJ where
 | aat
 | aaF
 | aaT
 | kP
 | kQ
 | kV
 | kY
 | k6
 | l6
 | lR
 | l7
 | l8
 | l9
 | mj
 | m7
 | nT
 | n6
 | pA
 | qk
 | q8
 | rq
 | rC
 | rN
 | rQ
 | sY
 | s4
 | s5
 | tI
 | s6
 | tT
 | s7
 | sJ
 | tv
 | uH
 | lZ
 | om
 | h7773
 | vX
 | vg
 | h21473
 | vW
 | h28323
 | h32433
def gJ.row:gJ→aYT
 | .aat=>⟨2370,2389,80495530196751944,0x28e2603a4656e54⟩
 | .aaF=>⟨2390,2409,0xf9469c19b9863c,0x21fe894e17f659f⟩
 | .aaT=>⟨2410,2419,0xee922aa6fec352,0x1eff8184d4a712c⟩
 | .kP=>⟨2420,2439,0xd28aff6311d93c,0x1a52aa17a200c95⟩
 | .kQ=>⟨2440,2459,0xbeb8e493d358e1,0x16440d31f9520f1⟩
 | .kV=>⟨2460,2479,0xadb5b5f73be6d7,88314402295386218⟩
 | .kY=>⟨2480,2499,0x98613c34a8f326,75580977671294650⟩
 | .k6=>⟨2500,2519,0x8847d91eac7fbf,0xe7d2adf917f50b⟩
 | .l6=>⟨2520,2529,0x7b4912a16ade38,0xc93bdc41198359⟩
 | .lR=>⟨2530,2539,0x75bb6a9f28f8fc,0xbe4d42573a1d57⟩
 | .l7=>⟨2540,2549,0x7065eff66bf144,0xb1980d09f47784⟩
 | .l8=>⟨2550,2559,0x6bfcd5ef169d7c,0xa7562d1ae58b34⟩
 | .l9=>⟨2560,2569,0x67b6e230093f68,0x9d62cb6f698f1f⟩
 | .mj=>⟨2570,2584,0x63dd572a4ca3e6,0x93bde56871940b⟩
 | .m7=>⟨2585,2589,0x5eb6d2250b1503,0x86c08e98cac21c⟩
 | .nT=>⟨2590,2599,0x5d1bb688d646a2,0x83265da321d05f⟩
 | .n6=>⟨2600,2600,0x5a06673904a74f,0x7a6d993286262d⟩
 | .pA=>⟨2601,2610,0x59b9e3dbbe7374,0x7a5c8387d06239⟩
 | .qk=>⟨2611,2620,0x56d2daf9e81b62,0x727d26c0359ab2⟩
 | .q8=>⟨2621,2639,0x546a03afc3ebfd,0x6dd9162595c015⟩
 | .rq=>⟨2640,2669,0x4ea52c8664f159,0x6366dbc040862e⟩
 | .rC=>⟨2670,2699,0x46e3fa6f4e6c0b,0x55627b039d421f⟩
 | .rN=>⟨2700,2749,0x407e41254c3346,0x49ae7b6f42cb70⟩
 | .rQ=>⟨2750,2799,0x38389d07305818,0x39b81ba31578a8⟩
 | .sY=>⟨2800,2899,0x316a41e4b3309d,0x2e14919bf19ff8⟩
 | .s4=>⟨2900,2949,8872442622423809,9173807193376184⟩
 | .s5=>⟨2950,2979,7987270307117438,7610274941597429⟩
 | .tI=>⟨2980,2999,7538749239604091,6908034803302175⟩
 | .s6=>⟨3000,3049,7276823856763379,6569338538207742⟩
 | .tT=>⟨3050,3099,5747479670950418,5916768739855770⟩
 | .s7=>⟨3100,3199,5245621618597394,5004749729248126⟩
 | .sJ=>⟨3200,3399,0xf8da1f5a11d37,0xd6d6924e7144a⟩
 | .tv=>⟨3400,3554,0x8e07cbdfe181c,0x99c8040f438ad⟩
 | .uH=>⟨3555,3999,0x75165f52b2eb6,0x716d568103f96⟩
 | .lZ=>⟨4000,4799,0x450c90e105601,0x42206b4855593⟩
 | .om=>⟨4800,7772,437785780857465,667070016592432⟩
 | .h7773=>⟨7773,7999,698804344963922,0xfaad6c38dfe1⟩
 | .vX=>⟨8000,14499,640008163332508,0xfc080066b8fc⟩
 | .vg=>⟨14500,21472,46894316540129,0x7ed9806efa33⟩
 | .h21473=>⟨21473,23999,21281848741227,74246611859481⟩
 | .vW=>⟨24000,28322,19998787150510,62656060897488⟩
 | .h28323=>⟨28323,32432,18715990635494,51439696596499⟩
 | .h32433=>⟨32433,33327,3323299909641,56675196335681⟩
end
end P1
end
section
namespace bzq
open xE Finset
open scoped BigOperators
private def bD5 (q r :ℤ) :ℤ :=
 984*q+3084*q*(q - 1)+1728*q*(q - 1)*(q - 2) +
  216*q*(q - 1)*(q - 2)*(q-3)+(24*r+4*(r - 1)*r*(r+1)) +
  q*(528*r+84*(r - 1)*r+4*(r - 2)*(r - 1)*r) +
  (684*r+36*(r - 1)*r)*q*(q - 1)+144*r*q*(q - 1)*(q - 2)
private def DW (n:ℤ) :ℤ:=bD5 (n/6) (n % 6)
def aTX (d n:ℕ) :ℤ :=
  DW n - DW (n-(d+1) :ℕ) - DW (n-(d+2) :ℕ) -
    DW (n-(d+3) :ℕ)+DW (n-(2*d+3) :ℕ) +
    DW (n-(2*d+4) :ℕ)+DW (n-(2*d+5) :ℕ) -
    DW (n-(3*d+6) :ℕ)
end bzq
end
