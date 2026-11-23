import ProximityPrize.SubmissionLower.ZZekYUb
import ProximityPrize.SubmissionLower.ZdSQxye
set_option Elab.async false
section
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace qPzVOea
open aR (Shape)
open qmb8rCe (sumN fullCost)
open qOPkAYa (base countedRank fastPart checked part_tail)
private abbrev a :Shape :=⟨87,27,12⟩
private abbrev full:=fullCost a 86
private abbrev part:=fastPart a 86
private theorem stockStep {n k x y :ℕ}
   (hx :sumN (base a) n=x∧sumN (countedRank a) n=x)
   (hy :sumN (fun i=>base a (n+i)) k=y∧sumN (fun i=>countedRank a (n+i)) k=y) :
   sumN (base a) (n+k)=x+y∧sumN (countedRank a) (n+k)=x+y :=
 ⟨checked hx.1 hy.1,checked hx.2 hy.2⟩
local notation "st!" start:arg count:arg ans:arg prev:arg =>
 stockStep (n:=start) (k :=count) (y :=ans) prev (And.intro rfl rfl)
local notation "ck!" fn:arg start:arg count:arg ans:arg prev:arg =>
 checked (f :=fn) (n:=start) (k :=count) (y :=ans) prev rfl
private theorem stock :sumN (base a) 88=991536∧sumN (countedRank a) 88=991536:= by
 let S (n x :ℕ) :=sumN (base a) n=x∧sumN (countedRank a) n=x
 have r0:S 0 0:=⟨rfl,rfl⟩
 have r8:S 8 13050:=st! 0 8 13050 r0
 have iu:S 16 82849:=st! 8 8 69799 r8
 have nJ:S 24 213679:=st! 16 8 130830 iu
 have r32 :S 32 356720:=st! 24 8 143041 nJ
 have Hz :S 40 487344 :=st! 32 8 130624 r32
 have zB:S 48 604656:=st! 40 8 117312 Hz
 have LH :S 56 708656:=st! 48 8 104000 zB
 have r64 :S 64 799344 :=st! 56 8 90688 LH
 have Vo:S 72 876720:=st! 64 8 77376 r64
 have Xe :S 80 940784 :=st! 72 8 64064 Vo
 have r88:S 88 991536:=st! 80 8 50752 Xe
 exact r88
private theorem full_rows :sumN full 88=87760322 := by
 have r0:sumN full 0=0:=rfl
 have r8:sumN full 8=1743942 :=ck! full 0 8 1743942 r0
 have iu:sumN full 16=11140350:=ck! full 8 8 9396408 r8
 have nJ:sumN full 24=28185406:=ck! full 16 8 17045056 iu
 have r32 :sumN full 32=45159218:=ck! full 24 8 16973812 nJ
 have Hz :sumN full 40=58659874 :=ck! full 32 8 13500656 r32
 have zB:sumN full 48=68978962 :=ck! full 40 8 10319088 Hz
 have LH :sumN full 56=76542466:=ck! full 48 8 7563504 zB
 have r64 :sumN full 64=81776370:=ck! full 56 8 5233904 LH
 have Vo:sumN full 72=85106658:=ck! full 64 8 3330288 r64
 have Xe :sumN full 80=86959314 :=ck! full 72 8 1852656 Vo
 have r88:sumN full 88=87760322 :=ck! full 80 8 801008 Xe
 exact r88
private theorem low_rows :sumN part 27=5072964 := by
 have r0:sumN part 0=0:=rfl
 have r8:sumN part 8=436794 :=ck! part 0 8 436794 r0
 have dK:sumN part 12=1118481 :=ck! part 8 4 681687 r8
 have iu:sumN part 16=2066532 :=ck! part 12 4 948051 dK
 have jV:sumN part 20=3148930:=ck! part 16 4 1082398 iu
 have nJ:sumN part 24=4259920:=ck! part 20 4 1110990 jV
 have tj:sumN part 27=5072964 :=ck! part 24 3 813044 nJ
 exact tj
private theorem tail_rows :sumN (fun i=>part (27+i)) 61=9073506:= by
 have h (i:ℕ) :part (27+i)=(174-2*(27+i))*1924+33306 :=
  part_tail (a :=a) (U:=86) (Nat.le_add_right 27 i) rfl rfl
 simp only [h]
 rfl
private theorem part_rows :sumN part 88=14146470 :=
 checked low_rows tail_rows
theorem proof :qOPkAYa.c1 := by
 change sumN (countedRank a) 88≤ sumN (base a) 88 ∧
  sumN full 88+sumN part 88≤87*sumN (base a) 88+15643160
 rw [stock.1,stock.2,full_rows,part_rows]
 exact ⟨Nat.le_refl _,Nat.le_refl _⟩
end qPzVOea
end
section
set_option autoImplicit true
namespace qVm3Zhc
noncomputable section
open Polynomial Finset

open P5_7 (midAgreement)
open baX (mix)
open aR (af extend)
open oR (qg)
open private OF from ProximityPrize.SubmissionLower.ZogIzOe
open private eK0 arV aPh from ProximityPrize.SubmissionLower.ZdSQxye
abbrev lambda :ℚ:=(262144 :ℚ)/midAgreement
abbrev jetRate (d:ℕ) :ℚ:=lambda*d
abbrev Ut (d:ℕ) :ℚ:=((262144-d:ℕ) :ℚ)/((midAgreement-d:ℕ) :ℚ)
abbrev Word:=OF
theorem regular {w T s d} (hw:Word w T s d) (hl:131071≤d) (hh:d≤133774)
   (f :af 2) (hf :Irreducible f) (hj:0<f.degreeOf 1)
   (hreg : ∀ γ∈T,qg 1 f (extend (s γ))) :
   let b:=(f.totalDegree :ℚ)
   let j:=(f.degreeOf 1 :ℚ)
   (T.card:ℚ)≤jetRate d*(4*b*j-2*j*j)+Ut d*j:= by
 let b:=f.totalDegree
 let j:=f.degreeOf 1
 let L:=jetRate d
 have hjb:j≤b:=f.degreeOf_le_totalDegree 1
 have hb:0<b:=hj.trans_le hjb
 have hL:1≤L:= by
   have hlam:1≤lambda := by norm_num [lambda]
   exact (show (1 :ℚ)≤d from Nat.one_le_cast.mpr (by omega)).trans
     (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg d))
 have hsum: (1 :ℚ)≤b+j:= by exact_mod_cast (show 1≤b+j by omega)
 have hpay :1≤L*((b:ℚ)+j) := by
   simpa only [one_mul] using mul_le_mul hL hsum (by decide : (0:ℚ)≤1) (by linarith only [hL])
 have htop:aPh d b j≤L*(2*j-1 :ℕ) :=min_le_right _ _
 have htot:arV d b=Ut d+2*L*(b-1 :ℕ) := by
   change Ut d+2*lambda*d*(b-1 :ℕ)=Ut d+2*(lambda*d)*(b-1 :ℕ)
   ring
 refine (eK0 hw hl hh hj f hf hj le_rfl le_rfl hreg).trans ?_
 change mix b j (arV d b) (aPh d b j)+1≤_
 unfold mix
 rw [htot]
 refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left htop (Nat.cast_nonneg (b-j)))
   le_rfl) le_rfl).trans ?_
 rw [Nat.cast_sub hjb,Nat.cast_sub (by omega :1≤2*j),Nat.cast_sub hb]
 push_cast
 nlinarith only [hpay]
end
end qVm3Zhc
end
section
set_option autoImplicit true
namespace qVm3Zhc
noncomputable section
open Polynomial Finset UniqueFactorizationMonoid
open P5 (K p)
open aR (af extend cK jet embed)
open oR (qg)
open gT (tK FW)
open pI (abM)
open bz3 (cFG)
open MvPolynomial (sum_weightedTotalDegree_le_of_prod_dvd weightedTotalDegree_one
 degreeOf_mul_eq degreeOf_prod_eq)
open private OF.distinct from ProximityPrize.SubmissionLower.ZogIzOe
open private dmf from ProximityPrize.SubmissionLower.ZdSQxye
open private QI bpk from ProximityPrize.SubmissionLower.BG
open scoped BigOperators
def blendTerm (B J:ℚ) :ℚ :=
 let r :=min B J
 if B=0 then 0 else 4*r-2*r*r/B
def coeff (B J L μ:ℚ) (t:Option ℚ) :ℚ×ℚ :=
 match t with
 | none=>(2*L*B+μ,2*L*J)
 | some v=>(4*L*B*v+μ,L*blendTerm B J*(1-v))
theorem cGf {B J L μ:ℚ} (hB:0≤B) (hJ:0≤J) (hL:0≤L)
    (hμ:0≤μ) {t:Option ℚ} (ht : ∀ v∈t,0≤v∧v≤1) :
    let c:=coeff B J L μ t
    0≤ c.1∧0≤ c.2 := by
  cases t with
  | none=>unfold coeff; exact ⟨by positivity,by positivity⟩
  | some v =>
    obtain ⟨hv,hv'⟩:=ht v (by simp)
    have hrest:=sub_nonneg.mpr hv'
    have hφ:0≤blendTerm B J:= by
      unfold blendTerm
      let r :=min B J
      change 0≤ if B=0 then 0 else 4*r-2*r*r/B
      split_ifs with hB0
      · exact le_rfl
      have hr :0≤ r :=le_min hB hJ
      have hdiv :2*r*r/B≤2*r :=(div_le_iff₀ (lt_of_le_of_ne hB (Ne.symm hB0))).mpr
        (mul_le_mul_of_nonneg_left (min_le_left B J) (by positivity))
      linarith only [hdiv,hr]
    unfold coeff
    exact ⟨by positivity,by positivity⟩
theorem blend_bound {B J L μ b j:ℚ} (hb:0≤b) (hj:0≤j) (hjb:j≤b)
    (hB:b≤B) (hJ:j≤J) (hL:0≤L) {t:Option ℚ}
    (ht : ∀ v∈t,0≤v∧v≤1) :
    let c:=coeff B J L μ t
    L*(4*b*j-2*j*j)+μ*j≤ c.1*j+c.2*b:= by
  let q:=4*b*j-2*j*j
  have hbj:=mul_le_mul_of_nonneg_right hB hj
  have hjb' := mul_le_mul_of_nonneg_right hJ hb
  cases t with
  | none =>
    have hq:q≤2*B*j+2*J*b:= by dsimp [q]; nlinarith only [hbj,hjb',sq_nonneg j]
    have h:=mul_le_mul_of_nonneg_left hq hL
    simp only [coeff]
    linarith only [h]
  | some v =>
    obtain ⟨hv,hw⟩:=ht v (by simp)
    by_cases hB0:B=0
    · have hb0:b=0:=le_antisymm (hB.trans_eq hB0) hb
      have hj0:j=0:=le_antisymm (hjb.trans_eq hb0) hj
      simp [hb0,hj0]
    have hBp:0<B:=lt_of_le_of_ne (hb.trans hB) (Ne.symm hB0)
    let r :=min B J
    have hjr :j≤ r :=le_min (hjb.trans hB) hJ
    have hrB:r≤B:=min_le_left B J
    have hfirst:q≤4*B*j:= by dsimp [q]; nlinarith only [hbj,sq_nonneg j]
    have hmono:4*j-2*j*j/B≤4*r-2*r*r/B:= by
      apply (le_of_mul_le_mul_right ?_ hBp)
      calc
        _=4*j*B-2*j*j:= by field_simp
        _≤4*r*B-2*r*r := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr hjr)
            (show 0≤4*B-2*(r+j) by linarith only [hjr,hrB])]
        _ = _:= by field_simp
    have hquot:2*j*j/B*b≤2*j*j:= by
      calc
        _≤(2*j*j/B)*B:=mul_le_mul_of_nonneg_left hB (by positivity)
        _ = _:=div_mul_cancel₀ _ hB0
    have hsecond:q≤blendTerm B J*b:= by
      unfold blendTerm
      rw [ite_eq_right hB0]
      exact (show q≤(4*j-2*j*j/B)*b by dsimp [q]; linarith only [hquot]).trans
        (mul_le_mul_of_nonneg_right hmono hb)
    have h:=add_le_add (mul_le_mul_of_nonneg_left hfirst hv)
      (mul_le_mul_of_nonneg_left hsecond (sub_nonneg.mpr hw))
    have hm:q≤v*(4*B*j)+(1-v)*(blendTerm B J*b) := by linarith only [h]
    have hp:=mul_le_mul_of_nonneg_left hm hL
    simp only [coeff]
    linarith only [hp]
theorem equation_bound {w T s d b j} (hw:Word w T s d) (hdl:131071≤d) (hdu:d≤133774)
    (G:tK) (hG:abM G b j) (hbchar :b<p)
    (hroot : ∀ γ∈T,FW G (s γ)=0)
    {B J:ℚ} (hbB: (b:ℚ)≤B) (hjJ: (j:ℚ)≤J) {t:Option ℚ}
    (ht : ∀ v∈t,0≤v∧v≤1) :
    let c:=coeff B J (jetRate d) (Ut d) t
    (T.card:ℚ)≤ c.1*j+(c.2+B)*b:= by
  classical
  obtain ⟨q,hq,hqb,hqj,hsolve⟩:=cFG G hG.1 hG.2.1 hG.2.2
  let _:StrongNormalizationMonoid (af 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M:=normalizedFactors q
  let A:=M.toFinset
  have hi (g:af 2) (hg:g∈A) :Irreducible g :=
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g∈A,g)∣q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq).dvd
  have hbs : (∑ g∈A,g.totalDegree)≤b:= by
    have h:=sum_weightedTotalDegree_le_of_prod_dvd (1 :Fin 2→ℕ) A id hq hdiv
    simp only [id_eq,weightedTotalDegree_one] at h
    exact h.trans hqb
  have hjs : (∑ g∈A,g.degreeOf 1)≤j:= by
    obtain ⟨r,hr⟩:=hdiv
    have hg0:=prod_ne_zero_iff.mpr fun g hg=>(hi g hg).ne_zero
    have hr0:r≠0:= fun hh=>hq (by simp [hr,hh])
    rw [hr,degreeOf_mul_eq hg0 hr0,degreeOf_prod_eq A (fun g=>g)
      (fun g hg=>(hi g hg).ne_zero)] at hqj
    exact (Nat.le_add_right _ _).trans hqj
  have hbf (g) (hg:g∈A) :g.totalDegree≤b :=
    (single_le_sum (fun x _=>Nat.zero_le x.totalDegree) hg).trans hbs
  have hjf (g) (hg:g∈A) :g.degreeOf 1≤j :=
    (single_le_sum (fun x _=>Nat.zero_le (x.degreeOf 1)) hg).trans hjs
  have he (g) (hg:g∈A) :=bpk g (hi g hg) (le_max_left 2 b)
    (max_lt (by decide :2<p) hbchar) ((hbf g hg).trans (le_max_right 2 b))
  let regularMarks (g:af 2) :=T.filter fun γ=>0<g.degreeOf 1∧qg 1 g (extend (s γ))
  let otherMarks (g:af 2) :=T.filter fun γ=>(QI g).eval (extend (s γ))=0
  let c:=coeff B J (jetRate d) (Ut d) t
  have hL:0≤jetRate d:= by positivity
  have hμ:0≤Ut d:= by unfold Ut; positivity
  have hB0:0≤B:=(Nat.cast_nonneg b).trans hbB
  obtain ⟨hc1,hc2⟩:=cGf hB0 ((Nat.cast_nonneg j).trans hjJ) hL hμ ht
  have hreg (g) (hg:g∈A) :
      ((regularMarks g).card:ℚ)≤ c.1*g.degreeOf 1+c.2*g.totalDegree := by
    by_cases hpos :0<g.degreeOf 1
    · have hW:Word w (regularMarks g) s d :=
        dmf hw (filter_subset _ _)
      refine (regular hW hdl hdu g (hi g hg) hpos (fun γ hγ=>(mem_filter.mp hγ).2.2)).trans ?_
      exact blend_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (by exact_mod_cast g.degreeOf_le_totalDegree 1)
        ((Nat.cast_le.mpr (hbf g hg)).trans hbB) ((Nat.cast_le.mpr (hjf g hg)).trans hjJ) hL ht
    · have hempty :regularMarks g = ∅ := by simp [regularMarks,hpos]
      rw [hempty,card_empty,Nat.cast_zero]
      exact add_nonneg (mul_nonneg hc1 (Nat.cast_nonneg _)) (mul_nonneg hc2 (Nat.cast_nonneg _))
  have hother (g) (hg:g∈A) :
      ((otherMarks g).card:ℚ)≤B*g.totalDegree := by
    let x (γ:K) :=extend (s γ)
    have hx :Set.InjOn x (otherMarks g:Set K) := fun _ ha _ hb h =>
      OF.distinct hw (filter_subset _ _ ha) (filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective h)
    have hd: ((otherMarks g).image x).card≤(QI g).natDegree := by
      apply card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
      exact (mem_roots (he g hg).1).mpr (mem_filter.mp hγ).2
    rw [card_image_of_injOn hx] at hd
    have hnat : (otherMarks g).card≤b*g.totalDegree := by
      by_cases hb:b=0
      · have hz :g.totalDegree=0:=Nat.eq_zero_of_le_zero (hb ▸ hbf g hg)
        simpa [hb,hz] using hd.trans (he g hg).2.1
      have hmax :max 2 b - 1≤b:= by omega
      exact (hd.trans ((he g hg).2.1.trans (Nat.mul_le_mul_left _ hmax))).trans_eq (Nat.mul_comm _ _)
    exact (by exact_mod_cast hnat : ((otherMarks g).card:ℚ)≤(b:ℚ)*g.totalDegree).trans
      (mul_le_mul_of_nonneg_right hbB (Nat.cast_nonneg _))
  have hsub:T⊆A.biUnion fun g=>regularMarks g∪otherMarks g:= by
    intro γ hγ
    have hvan:=hsolve _ (hroot γ hγ)
    have hM:MvPolynomial.eval (jet (extend (s γ))) M.prod=0:= by
      have hd:=map_dvd (MvPolynomial.eval (jet (extend (s γ)))) (prod_normalizedFactors hq).symm.dvd
      change cK q (extend (s γ))∣ _ at hd
      rwa [hvan,zero_dvd_iff] at hd
    rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hM
    obtain ⟨g,hg,hv⟩:=hM
    have hgA:g∈A:=Multiset.mem_toFinset.mpr hg
    refine mem_biUnion.mpr ⟨g,hgA,?_⟩
    rcases (he g hgA).2.2 _ hv with hz | hr
    · exact mem_union_right _ (mem_filter.mpr ⟨hγ,hz⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hr⟩)
  have hcard:=(card_le_card hsub).trans (card_biUnion_le.trans
    (sum_le_sum fun g _=>card_union_le (regularMarks g) (otherMarks g)))
  have hcardQ: (T.card:ℚ) ≤ ∑ g∈A,(((regularMarks g).card:ℚ)+(otherMarks g).card) := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ g∈A,(c.1*g.degreeOf 1+(c.2+B)*g.totalDegree) :=hcardQ.trans
      (sum_le_sum fun g hg=>(add_le_add (hreg g hg) (hother g hg)).trans_eq (by ring))
    _≤_:= by
      rw [sum_add_distrib,← mul_sum,← mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hjs) hc1)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hbs) (add_nonneg hc2 hB0))
end
end qVm3Zhc
end
