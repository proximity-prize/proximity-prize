import ProximityPrize.SubmissionLower.Z29Fskc
import ProximityPrize.SubmissionLower.ZHmpmKc
import ProximityPrize.SubmissionLower.ZtIIgWc
import ProximityPrize.SubmissionLower.ZBHfNie
import ProximityPrize.SubmissionLower.ZBG70hc
import ProximityPrize.SubmissionLower.ZGHT3gd
import ProximityPrize.SubmissionLower.Z3M0Hpe
import ProximityPrize.SubmissionLower.Zsr715c
import ProximityPrize.SubmissionLower.ZHCqaAd
set_option Elab.async false
section
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option quotPrecheck false in
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3284) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb (by decide +kernel) rfl) rfl
private theorem r0:bvj 3284 8=(0x37878992ee0:ℕ) :=numeric 3284 8 0x168d972c1b 0x37878992ee0 (by decide +kernel) rfl
private theorem r1 :bvj 3284 16=(0x6df870a7018:ℕ) :=asr r0,8,3292,8,0x37878992ee0,0x1624155e9b,0x3670e714138,0x6df870a7018
theorem total12 :bvj 3284 23=(0x9cb928e5908:ℕ) :=asr r1,16,3300,7,0x6df870a7018,0x13090ab642,0x2ec0b83e8f0,0x9cb928e5908
end q8kPhwd
end
section
set_option autoImplicit true
namespace q33KzTa
open P6_6_8 (edge c8J)
theorem proof :P6_6_8.c2 := by
  intro v hv
  change Test v
  obtain ⟨_,hj,ht,_⟩:=c8J hv
  rcases hv with rfl | ⟨hv,hb⟩
  · exact r0_0_0
  obtain ⟨b,j,t⟩:=v
  obtain ⟨hp,hmin,hmax⟩:=hv
  change b≤edge j at hb
  change j≤7 at hj
  change t≤2 at ht
  change 1≤t at hp
  change 3*t≤j at hmin
  change j≤3*b at hmax
  have hlo:3≤j:= by omega
  interval_cases j <;> interval_cases t <;> try omega
  · exact lane3_1 b (by omega) hb
  · exact lane4_1 b (by omega) hb
  · exact lane5_1 b (by omega) hb
  · exact lane6_1 b (by omega) hb
  · exact lane6_2 b (by omega) hb
  · exact lane7_1 b (by omega) hb
  · exact lane7_2 b (by omega) hb
end q33KzTa
end
section
set_option autoImplicit true
namespace qpkGSFe
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open private g3 g4 g6 g9 g11 g15 g17 g21 from ProximityPrize.SubmissionLower.ZtIIgWc
local notation "r!" a "," b "," c "," d "," e =>
  row (len:=b) (mass :=c) (cs :=List.map unpack d)
    a (by decide) (by decide) (by decide) e rfl rfl rfl (by decide)
private theorem r2 :ot 2 4 1 :=
  r! g3,94,0x59281edb6e3,[0x9249284080b9c7ed6,0xdb6da4187ae8c278f,0xc002c7c5107e],⟨rfl,rfl,rfl,trivial⟩
theorem lane4 (b:ℕ) (hlo:2≤b) (hhi:b≤22) :ot b 4 1 := by
  interval_cases b
  · exact r2
  · exact next_axis (b:=2) (j:=4) le_rfl le_rfl r2
  · exact r! g3,93,0x5cc76a1b52d,[0x102db6de5cc76a1b52d],⟨rfl,trivial⟩
  · exact r! g3,93,0x5eccc05a83b,[0x246dad0805eccc05a83b],⟨rfl,trivial⟩
  · exact r! g3,92,0x610c0ecd162,[0x48ff6090610c0ecd162],⟨rfl,trivial⟩
  · exact r! g3,92,0x61086830ab2,[0x48fb60a061086830ab2],⟨rfl,trivial⟩
  · exact r! g3,104,0x64d65e1e7ec,[0x92494642cd73e4cd6,0x9249241b457bc51e8,0x76db406c36e7492e],⟨rfl,rfl,rfl,trivial⟩
  · exact r! g3,104,0x668ae5ba2d2,[0x9249b64327ebf9d37,0x9249241c479eef980,0x3b6924071b5ad0c1b],⟨rfl,rfl,rfl,trivial⟩
  · exact r! g3,103,0x6844b4daee9,[0xdb6dea58a386535b1,0x792460fa12e87938],⟨rfl,rfl,trivial⟩
  · exact r! g3,103,0x69f08c148ea,[0x16db27c67039201706,0x48a02ecfa131e4],⟨rfl,rfl,trivial⟩
  · exact r! g3,102,0x6b061d0d19a,[0x123eda840e6b061d0d19a],⟨rfl,trivial⟩
  · exact r! g3,103,0x6df1f2d422b,[0x287ff0480906df1f2d422b],⟨rfl,trivial⟩
  · exact r! g3,102,0x6e88d10556b,[0x580801038500a06e88d10556b],⟨rfl,trivial⟩
  · exact r! g4,103,0x3adf5ec58d0,[0x160280480903adf5ec58d0],⟨rfl,trivial⟩
  · exact r! g4,103,0x3f179b696fb,[0x380600d03f179b696fb],⟨rfl,trivial⟩
  · exact r! g6,104,0x2da9dcf11da,[0x340580a02da9dcf11da],⟨rfl,trivial⟩
  · exact r! g9,105,0x2f543e6736b,[0x880f02f543e6736b],⟨rfl,trivial⟩
  · exact r! g11,106,0x2c19efab78f,[0x800f02c19efab78f],⟨rfl,trivial⟩
  · exact r! g15,109,0x204d5cd51b9,[0x780d0204d5cd51b9],⟨rfl,trivial⟩
  · exact r! g17,112,0x1cd2612b55c,[0x700d01cd2612b55c],⟨rfl,trivial⟩
  · exact r! g21,131,0x14740fdcaf8,[0x380500a014740fdcaf8],⟨rfl,trivial⟩
end qpkGSFe
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qcZ3orc
open aR (Shape)
open P6_6 P6_6_8 q2w4Sxc
open private width total from ProximityPrize.SubmissionLower.Zsr715c
abbrev C:=Certificate oL
private abbrev iL:Shape :=⟨0x39df27bb617ba,0x13bc369d92a21e,0x615f93175cf5⟩
private theorem credit_eq :Lw oL=iL:=rfl
theorem C8 {lo hi:Shape} {k bw:ℕ}
    (ho:CompanionTest oL lo k∨k=1) (hk :0<k∧k≤132)
    (hh:hi.t=1∨2≤lo.t) (ht:3*hi.t≤hi.j)
    (hf :selfFee oL hi k false=bw) (hc:bw≤dot iL lo) :
    C lo hi := .regular ⟨hk.1,hk.2,ho⟩ hh ht (by rwa [hf,credit_eq])
theorem order {r :Shape} {k :ℕ} {ws :List (List ℕ×ℕ)}
    (h:P6_6_8_3.ay oL {r with t:=0} k 0 ws)
    (hz :P6_6_8_3.layerMass oL {r with t:=0} k (width ws)=0)
    (hc:total ws<gG) :CompanionTest oL r k := by
  by_contra hh
  exact not_companion_down (x := {r with t:=0}) (y :=r)
    ⟨le_rfl,le_rfl,Nat.zero_le _⟩ hh (P6_6_8_3.reject h rfl rfl hz hc)
theorem root (h:C ⟨1,3,1⟩ ⟨133,56,16⟩) :q2w4Sxc.c1 := by
  intro v hv hj
  rcases hv with hv | hv
  · subst v
    exact h
  · have ht:=hv.1.1
    have h3:=hv.1.2.1
    omega
end qcZ3orc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace q7F4Ild
open aR (Shape)
open P6_6 P6_6_8 q2w4Sxc
abbrev state (b:ℕ) :Shape :=⟨b,5,1⟩
abbrev point (z :ℕ) :Shape :=⟨z % 256,z/256 % 64,z/ 16384 % 16⟩
abbrev low (z :ℕ) :=point z
abbrev high (z :ℕ) :=point (z/262144)
abbrev KN (z :ℕ) :=(low z,high z)
def Box (v :Shape) (z :ℕ) :Prop :=Certificate v (low z) (high z)
private theorem untrim {v lo hi:Shape} {z :ℕ}
    (h:trimBox lo hi=KN z) (hc:Box v z) :Certificate v lo hi:= by
  apply Certificate.trim
  rw [h]
  exact hc
theorem root {v :Shape} (z :ℕ) (hc:Box v z)
    (h:trimBox ⟨1,3,1⟩ (cap v)=KN z) :Certificate v ⟨1,3,1⟩ (cap v) :=
  untrim h hc
theorem cI {v :Shape} (z m:ℕ) {a b:ℕ}
    (l:Box v a) (r :Box v b)
    (ha :trimBox (low z) {high z with b:=m} = KN a)
    (hb:trimBox {low z with b:=m+1} (high z)=KN b) :Box v z :=
  Certificate.splitB m (untrim ha l) (untrim hb r)
theorem bV {v :Shape} (z m:ℕ) {a b:ℕ}
    (l:Box v a) (r :Box v b)
    (ha :trimBox (low z) {high z with j:=m} = KN a)
    (hb:trimBox {low z with j:=m+1} (high z)=KN b) :Box v z :=
  Certificate.rK m (untrim ha l) (untrim hb r)
theorem dSy {v :Shape} (z m:ℕ) {a b:ℕ}
    (l:Box v a) (r :Box v b)
    (ha :trimBox (low z) {high z with t:=m} = KN a)
    (hb:trimBox {low z with t:=m+1} (high z)=KN b) :Box v z :=
  Certificate.splitT m (untrim ha l) (untrim hb r)
abbrev unit (z :ℕ) :=2^(z % 64)
abbrev bucket (z :ℕ) :=z/64
private theorem jX {a b z :ℕ}
    (ha :a/unit z=bucket z) (hb:b/unit z=bucket z+1) :a≤b:= by
  by_contra! h
  have hd:=Nat.div_le_div_right h.le (c:=unit z)
  rw [ha,hb] at hd
  omega
theorem C8 {v c:Shape} {z :ℕ} (k q:ℕ) (hc:Lw v=c)
    (hk :0<k∧k≤132) (ht: (high z).t=1∨2≤(low z).t)
    (hj:3*(high z).t≤(high z).j)
    (ho:CompanionTest v (low z) k∨k=1)
    (hf :selfFee v (high z) k false/unit q=bucket q)
    (hb:dot c (low z)/unit q=bucket q+1) :Box v z :=
  Certificate.regular ⟨hk.1,hk.2,ho⟩ ht hj (hc ▸ jX hf hb)
theorem prune {v :Shape} {z k :ℕ} (hk :sharedOrder v=k) (h:CompanionTest v (low z) k) :
    Box v z :=Certificate.prune (hk.symm ▸ h)
theorem grade_five {v :Shape} (hv :W0 v) (hj:v.j=5) :
    2≤v.b∧v.b≤19∧v.t=1 := by
  rcases hv with h | ⟨hv,hb⟩
  · subst v
    contradiction
  · rw [hj] at hb
    change v.b≤19 at hb
    obtain ⟨ht,htj,hjb⟩:=hv
    omega
end q7F4Ild
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qJrCx9a
open aR (Shape aO)
open P6_6 P6_6_8 q2w4Sxc
open Finset EN
open scoped BigOperators
open private clip eL3 eiI WC bP5 byM aEH bvX from ProximityPrize.SubmissionLower.E6
private theorem untrimmed (d j t:ℕ) :
    (∑ r∈Finset.range (d+1),V7 r j t)=AJ.bmI ⟨d,j,t⟩:= by
  have h:=eL3 0 (d+1) j t 0 (d+1) d (Nat.zero_le _)
  simp only [clip,Nat.sub_zero,min_self,Nat.min_zero,Nat.Ico_zero_eq_range] at h
  have hp:wV.aWp 0 (d+1) j t (0,d+1,d) =
      AJ.bmI ⟨d,j,t⟩:= by
    simp [wV.aWp,wV.HY]
  rw [← hp,h]
  exact Finset.sum_congr rfl fun r hr=> by
    rw [min_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
private theorem flat_ge (x :Shape) :Gq x≤AJ.ahC Wk x := by
  unfold Gq AJ.ahC
  split
  next h =>
    rw [← untrimmed]
    exact Finset.sum_le_sum fun _ _=>eiI (min_le_left _ _) le_rfl le_rfl
  next _=>exact le_rfl
private def upper (v r :Shape) (k d:ℕ) :ℕ :=
  AJ.ahC Wk (used v r k d)
private theorem diM (v r :Shape) (k d:ℕ) :layerMass v r k d≤upper v r k d:= by
  rw [layerMass,aUJ]
  exact flat_ge _
private def ay (v r :Shape) (k start:ℕ) :List Chunk→Prop
  | []=>True
  | (xF,value) :: rest =>
    aEH (upper v r k) start xF=value∧ay v r k (start + xF.sum) rest
private theorem ayk {v r :Shape} {k start:ℕ} (cs :List Chunk)
    (h:ay v r k start cs) :
    WC (layerMass v r k) start (Fe cs)≤Jz cs := by
  induction cs generalizing start with
  | nil=>simp [WC,Fe,Jz]
  | cons c rest ih =>
    obtain ⟨xF,value⟩:=c
    rw [Fe,Jz,bP5]
    exact Nat.add_le_add ((byM (layer_anti v r k) xF start).trans
      ((bvX (diM v r k) xF start).trans_eq h.1)) (ih h.2)
theorem receipt {v r :Shape} {k :ℕ} (n m:ℕ) (cs :List Chunk)
    (hn:Fe cs=n) (hm:Jz cs=m) (hz :upper v r k n=0)
    (hlt:m<gG) (hc:ay v r k 0 cs) :CompanionTest v r k := by
  apply companion_of_mass (Nat.eq_zero_of_le_zero ((diM v r k n).trans_eq hz))
  have h:=ayk cs hc
  rw [hn,hm] at h
  simpa only [AJ.bOw,WC,Nat.zero_add] using h.trans_lt hlt
theorem top_mono {b:ℕ} {r :Shape} {k :ℕ}
    (h:CompanionTest ⟨b,7,1⟩ r k) :CompanionTest ⟨b,7,2⟩ r k := by
  unfold CompanionTest at h ⊢
  refine (Finset.sum_le_sum fun d _=>dNb ?_).trans_lt h
  have hs :aO ((⟨b,7,1⟩:Shape).scale (d+1)) ((⟨b,7,2⟩:Shape).scale (d+1)) :=
    Q5 (x :=⟨b,7,1⟩) (y :=⟨b,7,2⟩) ⟨le_rfl,le_rfl,(show 1≤2 by decide)⟩ _
  exact ⟨Nat.add_le_add_right hs.1 _,Nat.add_le_add_right hs.2.1 _,Nat.add_le_add_right hs.2.2 _⟩
theorem C8 {v lo hi c:Shape} {k f a :ℕ} (h:CompanionTest v lo k)
    (hk :0<k) (hk' : k≤132) (ht:hi.t=1∨2≤lo.t) (hj:3*hi.t≤hi.j)
    (hc:Lw v=c) (hf :selfFee v hi k false=f) (ha :dot c lo=a)
    (hle :f≤a) :Certificate v lo hi:= by
  refine Certificate.regular ⟨hk,hk',.inl h⟩ ht hj ?_
  rwa [hf,hc,ha]
theorem assemble {v :Shape} {b m t u:ℕ} (hc:cap v=⟨b,49,t⟩)
    (hb:trimBox ⟨1,3,2⟩ ⟨b,m,t⟩=(⟨2,6,2⟩,⟨b,m,u⟩))
    (hl:Certificate v ⟨1,3,1⟩ ⟨b,m,1⟩)
    (hh:Certificate v ⟨2,6,2⟩ ⟨b,m,u⟩)
    (hp:CompanionTest v ⟨1,m+1,1⟩ (sharedOrder v)) :Certificate v ⟨1,3,1⟩ (cap v) := by
  rw [hc]
  refine Certificate.rK m (Certificate.splitT 1 hl (Certificate.trim ?_)) (Certificate.prune hp)
  change Certificate v (trimBox ⟨1,3,2⟩ ⟨b,m,t⟩).1 (trimBox ⟨1,3,2⟩ ⟨b,m,t⟩).2
  rw [hb]
  exact hh
end qJrCx9a
end
