import ProximityPrize.SubmissionLower.ZBHfNie
import ProximityPrize.SubmissionLower.Z9vlvqb
import ProximityPrize.SubmissionLower.ZU4mhUb
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z9GIThc
import ProximityPrize.SubmissionLower.Z9HmSkb
import ProximityPrize.SubmissionLower.ZFx6vEd
import ProximityPrize.SubmissionLower.ZedfuCc
set_option Elab.async false
open _root_ renaming Finset.card_le_card → z1q, Finset.card_union_le → z2s, Finset.mem_union_left → zDk, Finset.sum_le_sum → zQk, List.replicate → zBf, Nat.add_le_add_left → z3b, Nat.lt_succ_of_le → zB1, Nat.mul_add → zws, Nat.mul_assoc → zfR, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
set_option Elab.async false
namespace q7F4Ild
open aR (Shape)
open P6_6 P6_6_8 q2w4Sxc
open private WC byM aEH bvX from ProximityPrize.SubmissionLower.E6
open private bSj.aTY from ProximityPrize.SubmissionLower.E6
open private eiI from ProximityPrize.SubmissionLower.E6
open private block_affine from ProximityPrize.SubmissionLower.Z8Nymda
open scoped BigOperators
abbrev prefixMass (v :Shape) (n:ℕ) :=mass v oL 1 n
private theorem bVH (v :Shape) (s n:ℕ) :
    massBlock v oL 1 s n=q33KzTa.block v s n:= by
  simp only [massBlock,q33KzTa.block,AJ.bOw]
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp [layerMass,aUJ,q33KzTa.stock_eq,Shape.scale,Shape.plus,FI.oL]
theorem Hw {b n a s :ℕ} (h:q33KzTa.tu 5 n a s)
    (hf :q33KzTa.AffineFits b 5 n) :prefixMass (state b) n=a - b*s := by
  have he :=block_affine (b:=b) (by decide :0<(5:ℕ)) hf
  rw [h.1,h.2] at he
  change mass (state b) oL 1 n= _
  rw [mass_eq_block,bVH]
  exact Nat.eq_sub_of_add_eq he
private theorem azU (v r :Shape) {k s :ℕ} (h:s≤k - 1) :
    massBlock v r k 0 s=prefixMass v s := by
  simp only [massBlock,AJ.bOw,Nat.zero_add]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Finset.mem_range.mp hd
  have hk :d+2 - k=0:= by omega
  simp [layerMass,Shape.plus,Shape.scale,FI.oL,hk]
private abbrev nQ:ℕ:=0x4000000
private abbrev width (z :ℕ) :=z % 64
private abbrev value (z :ℕ) :=z/64 % 0x100000
abbrev scale (z :ℕ) :=2^(z % 64)
abbrev blocks (z :ℕ) :=z/64 % 64
abbrev cutoff (z :ℕ) :=z/4096 % 512
abbrev payload (z :ℕ) :=z/2097152
private theorem homogeneous (x :Shape) :Gq x≤AJ.ahC Wk x := by
  by_cases h:x.b≤4025∧x.j≤1710∧x.t≤570
  · have h' : x.b≤Wk.b∧x.j≤Wk.j∧x.t≤Wk.t:=h
    simp only [Gq,AJ.ahC,ite_eq_left h']
    rw [← show wV.HY (4025 - x.b+1) (1710 - x.j) (570 - x.t) =
        AJ.bmI ⟨4025 - x.b,1710 - x.j,570 - x.t⟩ by
      simp only [wV.HY,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]]
    rw [bSj.aTY]
    exact zQk fun d _=>eiI (min_le_left _ _) le_rfl le_rfl
  · have h' : ¬ (x.b≤Wk.b∧x.j≤Wk.j∧x.t≤Wk.t) :=h
    simp only [Gq,ite_eq_right h',Nat.zero_le]
private def approximate (v r :Shape) (k e d:ℕ) :ℕ :=
  if d<e then q33KzTa.stock (used v r k d)
  else AJ.ahC Wk (used v r k d)
private theorem approximate_ge (v r :Shape) (k e d:ℕ) :
    layerMass v r k d≤approximate v r k e d:= by
  rw [layerMass,aUJ]
  unfold approximate
  split
  · rw [q33KzTa.stock_eq]
  · exact homogeneous _
private def sample (v r :Shape) (k e w s :ℕ) :ℕ :=
  aEH (approximate v r k e) s (zBf 6 w)
def bQw (v r :Shape) (k e u:ℕ) :ℕ→ℕ→ℕ→Prop
  | 0,_,_=>True
  | n+1,s,z=>sample v r k e (width z) s/u=value z ∧
      bQw v r k e u n (s+6*width z) (z/nQ)
def weights :ℕ→ℕ→ℕ
  | 0,_=>0
  | n+1,z=>value z+1+weights n (z/nQ)
def span:ℕ→ℕ→ℕ
  | 0,_=>0
  | n+1,z=>6*width z+span n (z/nQ)
private theorem round {a u q:ℕ} (hu:0< u) (h:a/u=q) :a≤u*(q+1) := by
  have hm:=Nat.mod_lt a hu
  have hd:=Nat.mod_add_div a u
  rw [h] at hd
  rw [zws,Nat.mul_one]
  omega
private theorem ayk (v r :Shape) (k e u:ℕ) (hu:0< u) (n s z :ℕ)
    (h:bQw v r k e u n s z) :
    massBlock v r k s (span n z)≤u*weights n z := by
  induction n generalizing s z with
  | zero=>simp [massBlock,AJ.CL,weights,span]
  | succ n ih =>
    obtain ⟨hd,ht⟩:=h
    let w:=width z
    have hrep: (zBf 6 w).sum=6*w:= by simp; omega
    have hs :=byM (layer_anti v r k) (zBf 6 w) s
    rw [hrep] at hs
    have hs' : massBlock v r k s (6*w)≤ sample v r k e w s := by
      have hs₁:massBlock v r k s (6*w) ≤
          aEH (layerMass v r k) s (zBf 6 w) := by
        simpa only [AJ.bOw,WC] using hs
      exact hs₁.trans (bvX (approximate_ge v r k e) _ _)
    rw [span,massBlock_add,weights,zws]
    exact Nat.add_le_add (hs'.trans (round hu hd)) (ih _ _ ht)
theorem companion {v r :Shape} {k s p:ℕ} (z m:ℕ)
    (hp:prefixMass v s=p) (hs :s≤k - 1)
    (hz :layerMass v r k (s+span (blocks z) (payload z))=0)
    (hc:bQw v r k (cutoff z) (scale z) (blocks z) s (payload z))
    (hm:p+scale z*weights (blocks z) (payload z)=m)
    (hlt:m<gG) :CompanionTest v r k := by
  apply companion_of_mass hz
  rw [mass_eq_block,massBlock_add,Nat.zero_add,azU v r hs,hp]
  rw [← hm] at hlt
  exact (z3b (ayk v r k _ _ (by positivity) _ _ _ hc) p).trans_lt hlt
end q7F4Ild
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qQCYsrb

open P6_6 P6_6_8 q2w4Sxc
open private g4 g5 g7 from ProximityPrize.SubmissionLower.ZBG70hc
local notation "m!" n "," x "," w =>
  segment (len:=n) (cost:=x) (word:=w) rfl rfl
local notation "o!" g "," h=>strict g (by decide) h rfl (by decide)
local notation "z!" h =>
  transport ⟨by decide,by decide,by decide⟩ ⟨by decide,by decide,by decide⟩ (by decide) h
local notation "b!" m "," x "," y=>Certificate.splitB m (Certificate.trim x) (Certificate.trim y)
local notation "j!" m "," x "," y=>Certificate.rK m (Certificate.trim x) (Certificate.trim y)
local notation "t!" m "," x "," y=>Certificate.splitT m (Certificate.trim x) (Certificate.trim y)
local notation "p!" vk "," vf "," h "," hc =>
  regular (k :=vk) (f :=vf) (by decide) h (by decide) (by decide) hc rfl (by decide)
private theorem r1 :Order 7 44 2 6 2 :=o! g4,(m! 100,0x417581c504a,0x29170b090808)
private theorem r2 :Order 7 25 1 3 1 :=o! g40a,(joinTail (m! 57,0x7a4617d8539,0x908070707070606) (m! 101,0x1957fa5d8fe,0x1a0f0d0a0b090908))
private theorem r3:Order 7 74 1 12 1 :=o! g75a,(joinTail (m! 12,0x14a4291915b,0x102010201020102) (joinTail (m! 18,0xe45bf9759b,0x203020203020202) (m! 38,0x47c28949a4,0xb060505050402)))
private theorem q7_1 :Lw ⟨7,6,1⟩=⟨0x14612da26c623,0x7ea9d701e7fd2,0x113a497b0dfe⟩:=rfl
private theorem q7_2 :Lw ⟨7,6,2⟩=⟨0x1457fb6650d4a,0x7db915885008b,0x33e5ae0e3c41⟩:=rfl
theorem s7 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨7,6,t⟩ ⟨1,3,1⟩ (cap ⟨7,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 11,(t! 1,(p! 25,0x1805e9d9c6d5ca,(.inl r2),q7_1),(p! 43,0x30cee112bb343f,(.inl (z! r1)),q7_1)),(Certificate.prune (z! r3)))
  · exact .trim (j! 11,(t! 1,(p! 25,0x1805e9d9c6d5ca,(.inl (bO4 r2)),q7_2),(p! 43,0x30cee112bb343f,(.inl (z! r1)),q7_2)),(Certificate.prune (z! r3)))
private theorem q8_1 :Lw ⟨8,6,1⟩=⟨0x13a5c2b3e2a91,0x786c9fb2ba108,0x104e5bc3c6da⟩:=rfl
private theorem q8_2 :Lw ⟨8,6,2⟩=⟨0x139c9df2b98a9,0x7786ddb0f8323,0x311e43edf6c1⟩:=rfl
theorem s8 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨8,6,t⟩ ⟨1,3,1⟩ (cap ⟨8,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 11,(t! 1,(p! 25,0x17d30d3852ef92,(.inl (z! r2)),q8_1),(p! 44,0x2f217a92912741,(.inl (z! r1)),q8_1)),(Certificate.prune (z! r3)))
  · exact .trim (j! 11,(t! 1,(p! 25,0x17d30d3852ef92,(.inl (z! r2)),q8_2),(p! 44,0x2f217a92912741,(.inl (z! r1)),q8_2)),(Certificate.prune (z! r3)))
private theorem r4 :Order 9 79 1 11 1 :=o! g5,(joinTail (m! 12,0x12252217a32,0x201020102010201) (joinTail (m! 17,0xc5f3ddc73f,0x302020302020201) (m! 42,0x4b5a61abe7,0xb07060505040202)))
private theorem q9_1 :Lw ⟨9,6,1⟩=⟨0x12f42400337c9,0x72770dce0db02,0xf69766c972b⟩:=rfl
private theorem q9_2 :Lw ⟨9,6,2⟩=⟨0x12eb0d56f5607,0x719c0a1338563,0x2e6c1cd59010⟩:=rfl
theorem s9 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨9,6,t⟩ ⟨1,3,1⟩ (cap ⟨9,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 10,(t! 1,(p! 22,0x15d9c0f38e4b27,(.inl (z! r2)),q9_1),(p! 38,0x2bfffff701e6eb,(.inl (z! r1)),q9_1)),(Certificate.prune (z! r4)))
  · exact .trim (j! 10,(t! 1,(p! 22,0x15d9c0f38e4b27,(.inl (z! r2)),q9_2),(p! 38,0x2bfffff701e6eb,(.inl (z! r1)),q9_2)),(Certificate.prune (z! r4)))
private theorem q10_1 :Lw ⟨10,6,1⟩=⟨0x11fa95e645282,0x6af793cf1af40,0xe518b641664⟩:=rfl
private theorem q10_2 :Lw ⟨10,6,2⟩=⟨0x11f1b630fdd17,0x6a2a5b60a3243,0x2b205c5fdc3c⟩:=rfl
theorem s10 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨10,6,t⟩ ⟨1,3,1⟩ (cap ⟨10,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 10,(t! 1,(p! 23,0x14aeb526b38b40,(.inl (z! r2)),q10_1),(p! 39,0x2a5e019b21424b,(.inl (z! r1)),q10_1)),(Certificate.prune (z! r4)))
  · exact .trim (j! 10,(t! 1,(p! 23,0x14aeb526b38b40,(.inl (z! r2)),q10_2),(p! 39,0x2a5e019b21424b,(.inl (z! r1)),q10_2)),(Certificate.prune (z! r4)))
private theorem r5:Order 11 83 1 11 1 :=o! g7,(m! 68,0x212a9fa49fa,0x1b090707070605)
private theorem q11_1 :Lw ⟨11,6,1⟩=⟨0x10c99f1d13b3d,0x6254528983b6a,0xd1267e4af3a⟩:=rfl
private theorem q11_2 :Lw ⟨11,6,2⟩=⟨0x10c0f0ef848b3,0x619668fb66053,0x275e3500fc06⟩:=rfl
theorem s11 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨11,6,t⟩ ⟨1,3,1⟩ (cap ⟨11,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 10,(t! 1,(p! 25,0x12c927e5942c2c,(.inl (z! r2)),q11_1),(p! 42,0x269dc7639ffdf9,(.inl (z! r1)),q11_1)),(Certificate.prune r5))
  · exact .trim (j! 10,(t! 1,(p! 25,0x12c927e5942c2c,(.inl (z! r2)),q11_2),(p! 42,0x269dc7639ffdf9,(.inl (z! r1)),q11_2)),(Certificate.prune (bO4 r5)))
end qQCYsrb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qs56oUd
noncomputable section
open aR dN wH lB agP
open Rl (acp aqk)
open P6_6_6 (Kq aNk)
open private cYA dgG from ProximityPrize.SubmissionLower.L
open private cYz from ProximityPrize.SubmissionLower.CU
open private c7I c5N from ProximityPrize.SubmissionLower.CF
open private a4g from ProximityPrize.SubmissionLower.E5
theorem reduce (f :af 4) (hf :P6_6.wm f)
    (D:af 3) (hD:D ≠0) (hcap:Gh D Kq.b Kq.j) :
    ∃ q:af 3,bbl f D q:= by
  rw [aNk] at hcap
  obtain ⟨q,hq,hdvd,hqcap,hsq,hroots⟩:=c7I D hD hcap
  have hgeom:=cyJ.proof q hsq (hqcap.1.trans_lt (by decide))
  have hproper :=c5N hf.1 hf.2.1 hq
  have hlocal (aI:Ideal GeoJets) (h:aqk f q aI) :
      bz9 f q aI h.minimal.isPrime :=cYz f q hgeom aI h
  have caps :Gh q Kq.b Kq.j:= by
    simpa only [aNk] using hqcap
  have hflow:aO (shape (acp q)) ⟨Kq.b,Kq.j+1,1⟩:= by
    rw [aNk]
    exact a4g hqcap (by decide) (by decide)
  exact ⟨q,hq,hdvd,caps,hgeom,hproper,hroots,hflow,
    fun aI h=>⟨ewr hf.1.ne_zero hproper h,
      cYA h.minimal.isPrime (hlocal aI h)⟩,
    fun aI h=>dgG h (hlocal aI h)⟩
end
end qs56oUd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qs56oUd
noncomputable section
open Polynomial MvPolynomial aR dN
open bat (Fy raw ail denominator numerator bqQ)
open lB (Po a9d Tn bF)
open Ex (C6)
open private c7d c7g from ProximityPrize.SubmissionLower.L
open private ceI cpc from ProximityPrize.SubmissionLower.Z9GIThc
open private specializes bO3 from ProximityPrize.SubmissionLower.L
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem Vi (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g:af 4} {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) (i:Fin P6_6.bf) :
    W w (numerator g i)≤w 0+P6_6.bf*(Fy (ail g)*(B - w 3)+Δ) := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  apply (Po _ _ _).trans
  unfold bqQ
  apply (Po _ _ _).trans
  apply (weightedTotalDegree_mul_le _ _ _).trans
  let k :=Fy (ail g)
  calc
    _≤k*(P6_6.bf - j.val)*(B - w 3) +
        (w 0+j.val*(k*(B - w 3)+Δ)) :=
      Nat.add_le_add (cpc g w _ hg) (ceI _ w Δ hshift hB hg _)
    _=w 0+(P6_6.bf - j.val+j.val)*(k*(B - w 3))+j.val*Δ:= by ring
    _≤_:= by
      rw [Nat.sub_add_cancel j.isLt.le,zws,← Nat.add_assoc]
      exact z3b (Nat.mul_le_mul_right Δ j.isLt.le) _
private theorem b2V {g Q:af 4} (hg:0<(shape g).t)
    (h : ∀ (w:Fin 4→ℕ) (Δ B:ℕ),(∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) →
      w 3≤B→W w g≤B →
      W w Q≤w 0+P6_6.bf*(Fy (ail g)*(B - w 3)+Δ)) :
    aO (shape Q) (P6_6_6.rH (shape g)) := by
  let p:=(shape g).iU
  let k :=Fy (ail g)
  have hch:bF p:=Tn g
  have hj:3≤p.j:= by
    have htop:3*p.t≤p.j:=hch.2
    have hpos :0<p.t:=hg
    omega
  have hb:1≤p.b:= by have hb:p.j≤p.b:=hch.1; omega
  let w:Fin 4→ℕ:=Pi.single 3 1
  have hbQ:Q.totalDegree≤1+P6_6.bf*(k*(p.b - 1)) := by
    have hbg:W (1 :Fin 4→ℕ) g≤p.b:= by
      rw [weightedTotalDegree_one]
      change g.totalDegree≤ max g.totalDegree (qE g)
      exact le_max_left _ _
    have h' := h 1 0 p.b (fun _=> by simp) hb hbg
    simpa only [weightedTotalDegree_one,Pi.one_apply,add_zero] using h'
  have hjQ:W Fin.val Q≤P6_6.bf*(k*(p.j-3)+1) := by
    have h' := h Fin.val 1 p.j (fun _=> by rfl) hj (by rw [← C6]; rfl)
    change W Fin.val Q≤0+P6_6.bf*(k*(p.j-3)+1) at h'
    rwa [zero_add] at h'
  have htQ:Q.degreeOf 3≤P6_6.bf*(k*(p.t - 1)+1) := by
    have h' := h w 1 p.t (fun i=> by fin_cases i <;> decide)
      (by change 1≤p.t; exact hg)
      (by simp only [w,weightedTotalDegree_piSingle]; exact le_rfl)
    simpa only [w,weightedTotalDegree_piSingle,show w 0=0 by decide,
      show w 3=1 by decide,zero_add] using h'
  unfold P6_6_6.rH
  change aO (shape Q) (if (shape g).t=1 then P6_6.ajN p else bY (P6_6.bf+4) p)
  have hbox (b j t:ℕ) (hB:Q.totalDegree≤b) (hJ:W Fin.val Q≤j)
      (hT:Q.degreeOf 3≤t) :aO (shape Q) ⟨max b j,j,min t (j/3)⟩:= by
    refine ⟨hB.trans (le_max_left _ _),?_,le_min hT ?_⟩
    · change qE Q≤j
      rwa [C6]
    · change Q.degreeOf 3≤j/3
      have htj:=(a9d Q).trans hJ
      omega
  split_ifs with hlin
  · have hk :k=1 := by simp [k,ail,hlin,Fy]
    have ht:p.t=1 :=hlin
    apply hbox
    · simpa only [hk,one_mul] using hbQ
    · rw [hk,one_mul,show p.j-3+1=p.j - 2 by omega] at hjQ
      exact hjQ.trans (Nat.le_add_left _ _)
    · simp only [hk,ht,Nat.sub_self,mul_zero,zero_add,mul_one] at htQ
      exact htQ.trans (Nat.le_succ _)
  · have hk :k=2 := by simp [k,ail,hlin,Fy]
    have hw:P6_6.bf≤P6_6.bf+4 :=Nat.le_add_right _ _
    have hscale (n:ℕ) :P6_6.bf*(2*n)≤2*(P6_6.bf+4)*n:= by
      rw [← Nat.mul_assoc,Nat.mul_comm P6_6.bf 2]
      exact Nat.mul_le_mul_right n (Nat.mul_le_mul_left 2 hw)
    apply hbox
    · rw [hk] at hbQ
      exact hbQ.trans (Nat.add_le_add_left (hscale _) 1)
    · simp only [hk,Nat.mul_add,mul_one] at hjQ
      exact hjQ.trans ((Nat.add_le_add (hscale _) hw).trans (Nat.le_add_right _ _))
    · simp only [hk,Nat.mul_add,mul_one] at htQ
      exact htQ.trans ((Nat.add_le_add (hscale _) hw).trans (Nat.le_add_right _ _))
theorem b0q {g:af 4} (hg:0<(shape g).t) :
    aO (shape (denominator g P6_6.bf)) (P6_6_6.rH (shape g)) := by
  apply b2V hg
  intro w Δ B _ _ hB
  have hp:=cpc g w (Fy (ail g)*P6_6.bf) hB
  refine hp.trans ?_
  calc
    _=P6_6.bf*(Fy (ail g)*(B - w 3)) := by ring
    _≤_:=Nat.le_add_left_of_le (zBI _ (Nat.le_add_right _ _))
theorem eFD {g:af 4} (hg:0<(shape g).t) (i:Fin P6_6.bf) :
    aO (shape (numerator g i)) (P6_6_6.rH (shape g)) :=
  b2V hg (fun w Δ _ hs h3 hB=>Vi w Δ hs h3 hB i)
theorem aX4 {g:af 4} (hg:0<(shape g).t) :
    aO (shape (raw (ail g) g P6_6.bf)) (P6_6_6.rH (shape g)) :=
  b2V hg (fun w Δ _ hs h3 hB=>ceI _ w Δ hs h3 hB _)
private theorem gBe (linear :Bool) (g:af 4)
    (hl:linear=true→separant (separant g)=0)
    (aI:Ideal GeoJets) (hp:aI.IsPrime) (hr :bC (separant g)∉aI) :
    bC (raw linear g P6_6.bf)∈aI↔bC (vU g)∈aI:= by
  cases linear with
  | false=>rw [c7d,vU]
  | true =>
    have hn:bC (separant g)^P6_6.bf∉aI :=
      fun h=>hr (hp.mem_of_pow_mem _ h)
    unfold vU
    rw [c7g g (hl rfl)]
    simp only [bC,map_mul,map_pow] at hn ⊢
    exact ⟨fun h=>aI.mul_mem_left _ h,fun h=>(hp.mem_or_mem h).resolve_left hn⟩
theorem d9D (g:af 4) (hg:0<(shape g).t) :Nonempty (Li g) := by
  have hp:P6_6.bf<K1.p:= by decide
  refine ⟨{
    denom:=denominator g P6_6.bf
    Fr :=numerator g
    test :=raw (ail g) g P6_6.bf
    denom_box :=b0q hg
    numer_box :=eFD hg
    aX4 :=aX4 hg
    test_iff := fun aI hprime _ hr=>gBe _ _ (bO3 g) aI hprime hr
    ar5 := ?_ }⟩
  intro L _ _ S hd hs hr
  exact specializes g S (n:=P6_6.bf) (zB1 hd) hp.le hs hr
theorem donor_taylor (g:af 4) (hg:0<(shape g).t) :
    Nonempty (Rl.Li g) := by
  have hp:aR.bf≤K1.p:= by decide
  refine ⟨{
    denom:=denominator g aR.bf
    Fr :=numerator g
    test :=raw (ail g) g aR.bf
    denom_box :=bat.b0q hg
    numer_box :=bat.eFD hg
    aX4 :=bat.aX4 hg
    test_iff := fun aI hprime _ hr =>
      bat.gBe _ _ (bO3 g) aI hprime hr
    ar5 := ?_ }⟩
  intro L _ _ S hd hs hr
  exact specializes g S (zB1 hd) hp hs hr
end
end qs56oUd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qs56oUd
noncomputable section
open Polynomial
open P6 (K I node)
open P6_6 (Messages wm acX gZ mV)
open P6_6_6 (rH)
open P6_6_5 (bv5)
open qQ76XXb (bgc)
open aR (af Shape extend shape Dd ceilDiv)
open dN (bC DA)
open wH (qg)
open Rl (bkW bbz bTH acp aYV)
open scoped BigOperators
open Finset
open private cXX from ProximityPrize.SubmissionLower.J
def c1 :Prop :=
  ∀ (Γ:Finset K) (s :K→K[X]) (f :af 4) (D q:af 3),
    0<(shape f).t→bbl f D q → ∀ T:Li f,
    Set.InjOn s (Γ:Set K)→(∀ γ∈Γ,(s γ).natDegree≤gZ) →
    (∀ γ∈Γ,Dd f (extend (s γ))∧qg f (extend (s γ))) →
    ∃ C:DA Γ,C.qv s ∧
      (∀ γ∈Γ,bkW f q T.test (extend (s γ))→γ∈C.union) ∧
      32*C.total≤boc (shape f) ∧
      32*C.n≤bnI (shape f)
def c2 :Prop :=
  ∀ (Γ:Finset K) (s :K→K[X]) (f :af 4),
    wm f→acX (shape f)→Rl.Li f →
    Set.InjOn s (Γ:Set K)→(∀ γ∈Γ,(s γ).natDegree≤gZ) →
    (∀ γ∈Γ,Dd f (extend (s γ))∧qg f (extend (s γ))) →
    ∃ C F:DA Γ,C.uG s∧bTH F s ∧
      (∀ i,0<C.degree i)∧(∀ i,0<F.degree i) ∧
      (∀ γ∈Γ,aYV f (extend (s γ))→γ∈C.union∪F.union) ∧
      2*C.total≤133671*(shape f).iU.b*(wH.rH (shape f)).b ∧
      F.total≤(shape f).iU.b*(wH.rH (shape f)).b^2
private theorem ee8:mV=46402 := by decide
private theorem d1C:P6.t=82317:= by decide
private theorem ePx {w Γ s} {x :Shape} (C:DA Γ) (h:Messages w Γ s)
    (hc:C.qv s) (hb:32*C.total≤boc x)
    (hn:32*C.n≤bnI x) :
    C.union.card≤ ceilDiv (82317*boc x) (32*46402) +
      ceilDiv (bnI x) 32 := by
  have hcap:46402*C.union.card≤82317*C.total+46402*C.n:= by
    classical
    calc
      _≤46402 * ∑ i,(C.dO i).card:=zBI _ card_biUnion_le
      _ = ∑ i,46402*(C.dO i).card:=mul_sum ..
      _ ≤ ∑ i:Fin C.n,(82317*C.degree i+46402) :=sum_le_sum fun i _ =>
        bv5 (h.mono (C.subset i)) (C.degree i) (fun j=>hc i (node j) (w j))
      _ = _:= by simp [DA.total,sum_add_distrib,mul_sum,Nat.mul_comm]
  unfold ceilDiv
  omega
private theorem gBx {w Γ s d} (h:Messages w Γ s)
    (hs :bbz Γ s d) (hd:0<d) :Γ.card≤8*d:= by
  classical
  have hsection (i:I) (hi : ∃ γ∈Γ,(s γ).eval (node i)≠w i) :
      (Γ.filter (fun γ=>(s γ).eval (node i)=w i)).card≤4*d:= by
    obtain ⟨C,hC,hc,hpos,hdeg⟩:=hs (node i) (w i) hi
    have hH :=h.mono (Finset.filter_subset (fun γ=>(s γ).eval (node i)=w i) Γ)
    exact (z1q hC).trans ((bgc C hH hc hpos).trans
      (zBI 4 hdeg))
  have :=bv5 h (4*d) hsection
  omega
private theorem gBy {w Γ s} (C:DA Γ) (h:Messages w Γ s)
    (hc:bTH C s) (hd : ∀ i,0<C.degree i) :C.union.card≤8*C.total:= by
  classical
  calc
    _ ≤ ∑ i,(C.dO i).card:=Finset.card_biUnion_le
    _ ≤ ∑ i,8*C.degree i:=zQk fun i _ =>
      gBx (h.mono (C.subset i)) (hc i) (hd i)
    _ = _:= by simp [DA.total,Finset.mul_sum]
private theorem scaled_max {a b c d:ℕ} (ha :2*a≤3*c) (hb:2*b≤3*d) :
    2*max a b≤3*max c d:= by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact hb.trans (zBI _ (le_max_right _ _))
  · rw [max_eq_left h]
    exact ha.trans (zBI _ (le_max_left _ _))
private theorem donor_chart_b (x :Shape) :
    2*(wH.rH x).b≤3*(rH x).b:= by
  let p:=x.iU
  unfold wH.rH rH
  split_ifs
  · change 2*max (1+133672*(p.b - 1)) (3+133672*(p.j - 2)) ≤
      3*max (1+133426*(p.b - 1)) (3+133426*(p.j - 2))
    exact scaled_max (by omega) (by omega)
  · change 2*max (1+267352*(p.b - 1)) (267352*(p.j-3)+133676+3) ≤
      3*max (1+266860*(p.b - 1)) (266860*(p.j-3)+133430+3)
    exact scaled_max (by omega) (by omega)
theorem of_children (h1 :c1) (h2 :c2) :P6_6_6.c2 := by
  classical
  intro w Γ s hm f hf helig hon D hD hbox hDmark
  obtain ⟨q,hq⟩:=reduce f hf D hD hbox
  obtain ⟨T⟩:=d9D f hf.2.1
  obtain ⟨U⟩:=donor_taylor f hf.2.1
  obtain ⟨A,hA,hcoverA,hcurve,hcomp⟩ :=
    h1 Γ s f D q hf.2.1 hq T hm.distinct hm.degree hon
  obtain ⟨C,F,hC,hF,hposC,hposF,hcoverI,hdegC,hdegF⟩ :=
    h2 Γ s f hf helig U hm.distinct hm.degree hon
  have hcover :Γ⊆A.union∪(C.union∪F.union) := by
    intro γ hγ
    let S:=extend (s γ)
    have hfS:=(hon γ hγ).1
    have hrS:=(hon γ hγ).2
    have hdS:S.natDegree≤gZ:=Polynomial.natDegree_map_le.trans (hm.degree γ hγ)
    obtain ⟨aI,hZ,hle⟩:=cXX hfS hrS (hq.roots S (hDmark γ hγ))
    by_cases hE :bC T.test∈aI
    · by_cases hflow:bC (acp q)∈aI
      · have hfZ:bC f∈aI:=hZ.minimal.le (Ideal.subset_span (by simp))
        have hmem:bC (vU f)∈aI :=
          (T.test_iff aI hZ.minimal.isPrime hfZ hZ.regular).mp hE
        have hI:aYV f S:=dPy f hf aI hZ.minimal.isPrime (hq.simple aI hZ).1
          hfZ hZ.regular (hq.invariant aI hZ hflow) hmem S hle hrS hdS
        exact Finset.mem_union_right _ (hcoverI γ hγ hI)
      · exact zDk _ (hcoverA γ hγ ⟨aI,hZ,hle,Or.inr hflow⟩)
    · exact zDk _ (hcoverA γ hγ ⟨aI,hZ,hle,Or.inl hE⟩)
  have hAcard:=ePx A hm hA hcurve hcomp
  have hCcard:=bgc C hm hC hposC
  have hFcard:=gBy F hm hF hposF
  have hsum:=(z1q hcover).trans (z2s _ _)
  have hsumI:=z2s C.union F.union
  let p:=(shape f).iU
  let h:=rH (shape f)
  change Γ.card≤ ceilDiv (P6.t*boc (shape f)) (32*mV) +
    ceilDiv (bnI (shape f)) 32+20*p.b*h.b^2 +
    5*gZ*p.b*h.b+1
  rw [ee8,d1C]
  let H :=(wH.rH (shape f)).b
  have hh:2*H≤3*h.b:=donor_chart_b (shape f)
  have hreserveC:C.union.card≤5*(gZ*p.b*h.b) := by
    have hbudget:4*(2*133671*p.b*H)≤18*(gZ*p.b*h.b) := calc
      _=(2*p.b)*((2*133671)*(2*H)) := by ring
      _≤(2*p.b)*((3*gZ)*(3*h.b)) :=
        zBI _ (Nat.mul_le_mul (by decide) hh)
      _ = _:= by ring
    have hcount:=hCcard.trans (show 4*C.total≤2*133671*p.b*H by
      simpa only [← zfR] using zBI 2 hdegC)
    omega
  have hreserveF:F.union.card≤20*(p.b*h.b^2) := by
    have hbudget:8*(p.b*H^2)≤18*(p.b*h.b^2) := calc
      _=(2*p.b)*((2*H)*(2*H)) := by ring
      _≤(2*p.b)*((3*h.b)*(3*h.b)) :=
        zBI _ (Nat.mul_le_mul hh hh)
      _ = _:= by ring
    exact hFcard.trans ((zBI _ hdegF).trans (hbudget.trans (by omega)))
  rw [zfR 20,zfR 5,zfR 5]
  omega
end
end qs56oUd
end
