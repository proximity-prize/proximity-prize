import ProximityPrize.SubmissionLower.Z7ee2Qb
import ProximityPrize.SubmissionLower.ZMwIPwd
import ProximityPrize.SubmissionLower.ZLMe53d
import ProximityPrize.SubmissionLower.ZrHwqOb
import ProximityPrize.SubmissionLower.ZVHUUZd
import ProximityPrize.SubmissionLower.ZffaUPa
set_option Elab.async false
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
namespace qXncema
theorem proof :q1yhP8b.c1 :=
  qA0rFHd.of_children qYur1ad.proof qnKm5Ba.proof qWpt85c.proof
end qXncema
end
section
set_option autoImplicit true
namespace qXzfTzc
noncomputable section
open aR (ao Shape)
open aFN (Slot)
open qzLARrc (derivativeIndex)
open qmb8rCe (rankCut cutMatrix cap sumN_eq)
open MvPolynomial Finset
open scoped BigOperators
private theorem cp3 {a :Shape} {q:ℕ} (s :Slot a q) :
    s.1.val+s.2.val≤q∧s.2.val+2*s.1.val≤a.j∧s.1.val≤a.t:= by
  have hc:=s.1.isLt
  have hb:=s.2.isLt
  simp only [Nat.lt_succ_iff,le_min_iff] at hc hb
  omega
private def aQs (a :Shape) (q:ℕ) (e :Fin 2 →₀ ℕ)
    (hq:e 0+e 1≤q) (hj:weight e≤a.j) (ht:e 1≤a.t) :Slot a q:= by
  unfold weight at hj
  let c:Fin (min q (min a.t (a.j/2))+1) :=
    ⟨e 1,by simp only [Nat.lt_succ_iff,le_min_iff]; omega⟩
  exact ⟨c,⟨e 0,by
    change _< min (q-e 1) (a.j-2*e 1)+1
    simp only [Nat.lt_succ_iff,le_min_iff]
    omega⟩⟩
private abbrev cV {a :Shape} {q:ℕ} (s :Slot a q) :=
  q-(s.2.val+(s.1.val-(a.j-q)))
private abbrev up (a :Shape) (n:ℕ) :=min a.t (min n (a.j-n))
private abbrev low (q d n:ℕ) :=n-(q-d)
private abbrev bound (a :Shape) (q d h n:ℕ) :=
  min (up a n+1-low q d n) (min a.t (min n (h-1-n))+1)
private abbrev length (a :Shape) (q d h:ℕ) :=min (q+1) (min (a.j+1-d) h)
private abbrev Count (a :Shape) (q d h:ℕ) :=
  Σ n:Fin (length a q d h),Fin (bound a q d h n)
private abbrev Good (a :Shape) (q d h:ℕ) :=
  {s :Slot a q // d≤ s.1.val+s.2.val∧up a (cV s)<s.1.val+(h-cV s)}
private theorem grade_bounds {a :Shape} {q d:ℕ} (hq:q≤a.j) (s :Slot a q)
    (hd:d≤ s.1.val+s.2.val) :
    let n:=cV s
    n+s.2.val+(s.1.val-(a.j-q))=q ∧
      low q d n≤ s.1.val∧s.1.val≤up a n∧n+d≤a.j:= by
  obtain ⟨hb,hj,ht⟩:=cp3 s
  dsimp [cV,low,up]
  omega
private theorem good_card (a :Shape) (q d h:ℕ) (hq:q≤a.j) :
    Fintype.card (Good a q d h)≤ cap a q d h:= by
  have hc (s :Good a q d h) :cV s.val<length a q d h ∧
      up a (cV s.val)-s.val.1.val<bound a q d h (cV s.val) := by
    obtain ⟨he,hl,hu,hn⟩:=grade_bounds hq s.val s.property.1
    have hg:=s.property.2
    dsimp only [length,bound]
    have hu' : up a (cV s.val)≤a.t∧up a (cV s.val)≤ cV s.val := by
      dsimp only [up]
      omega
    omega
  let f (s :Good a q d h) :Count a q d h :=
    ⟨⟨cV s.val,(hc s).1⟩,⟨up a (cV s.val)-s.val.1.val,(hc s).2⟩⟩
  have hf :Function.Injective f := by
    intro s t hst
    have hn:=congrArg (fun i:Count a q d h=>i.1.val) hst
    have hc:=congrArg (fun i:Count a q d h=>i.2.val) hst
    change cV s.val=cV t.val at hn
    change up a (cV s.val)-s.val.1.val=up a (cV t.val)-t.val.1.val at hc
    obtain ⟨hs,_,hus,_⟩:=grade_bounds hq s.val s.property.1
    obtain ⟨ht,_,hut,_⟩:=grade_bounds hq t.val t.property.1
    have he :s.val.1.val=t.val.1.val := by rw [← hn] at hc hut; omega
    apply Subtype.ext
    exact Sigma.ext (Fin.ext he) ((Fin.heq_ext_iff (by rw [he])).mpr (by omega))
  apply (Fintype.card_le_of_injective f hf).trans
  rw [cap,sumN_eq,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Fin.sum_univ_eq_sum_range (bound a q d h) _).le
private theorem bad_relation (a :Shape) (q d h:ℕ) (hq:q≤a.j) (s :Slot a q)
    (hd:d≤ s.1.val+s.2.val) (hb:s.1.val+(h-cV s)≤up a (cV s)) :
    ∃ p:Poly,Bounds d q a.j a.t p ∧
      orderGe (derivativeIndex s+1) (p-monomial (ex s.2.val s.1.val) 1) ∧
      project a q h p=0:= by
  let n:=cV s
  let c:=s.1.val
  let b:=s.2.val
  let r :=h-n
  let i:=min r (a.j-q-c)
  let j:=r-i
  obtain ⟨he,_,_,_⟩:=grade_bounds hq s hd
  change n+b+(c-(a.j-q))=q at he
  change c+r≤up a n at hb
  have hr :c+r≤a.t∧c+r≤n∧c+r≤a.j-n:= by
    simpa only [up,le_min_iff] using hb
  have hij:i+j=r := by dsimp [i,j]; omega
  have hj:j≤b:= by dsimp [i,j]; omega
  let p:=relation b c (n-c) r i j
  refine ⟨p,?_,relation_lead b c (n-c) r i j hj,?_⟩
  · have hp:=relation_bounds b c (n-c) r i j
    apply hp.mono
    · change d≤ c+b at hd
      omega
    · omega
    · have hi:i≤a.j-q-c:=min_le_right _ _
      omega
    · omega
  · funext t
    rw [project_apply]
    split
    next ht =>
      apply (relation_zero b c (n-c) r i j).coeff_eq_zero
      have :derivativeIndex t<h:=ht
      change t.2.val+2*t.1.val<h at this
      simp only [weight,ex_zero,ex_one]
      dsimp [r] at hij
      omega
    · rfl
private def gen (a :Shape) (q d h:ℕ) (s :Good a q d h) :Slot a q→ao :=
  project a q h (monomial (ex s.val.2.val s.val.1.val) 1)
theorem rank_le (a :Shape) (q d h:ℕ) (hq:q≤a.j) :
    rankCut a q d h≤ cap a q d h:= by
  let T:=Submodule.span ao (Set.range (gen a q d h))
  have aux (k :ℕ) : ∀ s :Slot a q,a.j-derivativeIndex s=k →
      d≤ s.1.val+s.2.val→project a q h (monomial (ex s.2.val s.1.val) 1)∈T:= by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s hk hs
      by_cases hg:up a (cV s)<s.1.val+(h-cV s)
      · exact Submodule.subset_span ⟨⟨s,hs,hg⟩,rfl⟩
      obtain ⟨p,hp,hlead,hzero⟩:=bad_relation a q d h hq s hs (Nat.le_of_not_gt hg)
      let m:Poly :=monomial (ex s.2.val s.1.val) 1
      obtain ⟨hq',hj',ht'⟩:=cp3 s
      have hm:Bounds d q a.j a.t m :=
        (bounds_mon s.2.val s.1.val).mono (by omega) (by omega) hj' ht'
      have hf :Bounds d q a.j a.t (m-p) := by simpa only [sub_eq_add_neg] using hm.add hp.neg
      have hw:orderGe (derivativeIndex s+1) (m-p) := by simpa using hlead.neg
      change project a q h m∈T
      rw [← sub_zero (project a q h m),← hzero,← map_sub,(m-p).as_sum,map_sum]
      apply Submodule.sum_mem
      intro e he
      obtain ⟨hd',hq'',hj'',ht''⟩:=hf e he
      let t:=aQs a q e hq'' hj'' ht''
      have hlt:a.j-derivativeIndex t<k := by
        have hl:=hw e he
        change a.j-weight e<k
        have hs' : derivativeIndex s≤a.j:=hj'
        omega
      have hi:=ih _ hlt t rfl (by change d≤e 1+e 0; omega)
      change project a q h (monomial (ex (e 0) (e 1)) 1)∈T at hi
      rw [ex_unique] at hi
      rw [show monomial e ((m-p).coeff e)=(m-p).coeff e•monomial e 1 by
        rw [smul_monomial,smul_eq_mul,mul_one],map_smul]
      exact T.smul_mem _ hi
  rw [rankCut,Matrix.rank_eq_finrank_span_cols]
  have hs :Submodule.span ao (Set.range (cutMatrix a q d h).col)≤T:= by
    rw [Submodule.span_le,Set.range_subset_iff]
    intro s
    by_cases hd:d≤ s.1.val+s.2.val
    · rw [← project_col s hd]
      exact aux _ s rfl hd
    · have he : (cutMatrix a q d h).col s=0:= by
        funext r
        simp [cutMatrix,hd]
      rw [he]
      exact T.zero_mem
  exact (Submodule.finrank_mono hs).trans
    ((finrank_range_le_card (gen a q d h)).trans (good_card a q d h hq))
end
end qXzfTzc
end
section
set_option autoImplicit true
set_option maxRecDepth 2048
namespace qmb8rCe
open qlc9qed (Bank)
open qzLARrc (oneDebit)
private theorem sum_add (f g:ℕ→ℕ) (n:ℕ) :
    sumN (fun i=>f i+g i) n=sumN f n+sumN g n:= by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [sumN,ih]; ac_rfl
private theorem sum_append (f :ℕ→ℕ) (n k :ℕ) :
    sumN f (n+k)=sumN f n+sumN (fun i=>f (n+i)) k := by
  induction k with
  | zero=>simp [sumN]
  | succ k ih =>
    change sumN f (n+k)+f (n+k) =
      sumN f n+(sumN (fun i=>f (n+i)) k+f (n+k))
    rw [ih,Nat.add_assoc]
private theorem checked {f :ℕ→ℕ} {n k x y :ℕ} (hx :sumN f n=x)
    (hy :sumN (fun i=>f (n+i)) k=y) :sumN f (n+k)=x+y := by
  rw [sum_append,hx,hy]
set_option quotPrecheck false in
local notation "ck!" fn:arg start:arg count:arg ans:arg prev:arg =>
  checked (f :=fn) (n:=start) (k :=count) (y :=ans) prev (by decide +kernel)
private abbrev full:=fullCost box 640
private abbrev part:=partCost box 640
private theorem xHa0:sumN full 0=0:=rfl
private theorem xHa1:sumN full 8=7527702:=ck! full 0 8 7527702 xHa0
private theorem xHa2:sumN full 16=49915918:=ck! full 8 8 42388216 xHa1
private theorem xHa3:sumN full 24=0x7d395d6:=ck! full 16 8 81391048 xHa2
private theorem xHa4:sumN full 32=0xd0db106:=ck! full 24 8 87694128 xHa3
private theorem xHa5:sumN full 40=0x11a9cb36:=ck! full 32 8 77339184 xHa4
private theorem xHa6:sumN full 48=0x15a4d166:=ck! full 40 8 66782768 xHa5
private theorem xHa7:sumN full 56=0x19054396:=ck! full 48 8 56652336 xHa6
private theorem xHa8:sumN full 64=0x1bd1a1c6:=ck! full 56 8 46947888 xHa7
private theorem xHa9:sumN full 72=0x1e106bf6:=ck! full 64 8 37669424 xHa8
private theorem xHa10:sumN full 80=0x1fc82226:=ck! full 72 8 28816944 xHa9
private theorem xHa11:sumN full 88=0x20ff4456:=ck! full 80 8 20390448 xHa10
private theorem full_rows :sumN full 88=0x20ff4456 :=xHa11
private theorem xHa12:sumN part 0=0:=rfl
private theorem xHa13:sumN part 8=1882734:=ck! part 0 8 1882734 xHa12
private theorem xHa14:sumN part 12=4899531:=ck! part 8 4 3016797 xHa13
private theorem xHa15:sumN part 15=8027123:=ck! part 12 3 3127592 xHa14
private theorem xHa16:sumN part 17=10396247:=ck! part 15 2 2369124 xHa15
private theorem xHa17:sumN part 19=12912998:=ck! part 17 2 2516751 xHa16
private theorem xHa18:sumN part 21=15522058:=ck! part 19 2 2609060 xHa17
private theorem xHa19:sumN part 23=18179837:=ck! part 21 2 2657779 xHa18
private theorem xHa20:sumN part 24=19516526:=ck! part 23 1 1336689 xHa19
private theorem xHa21:sumN part 25=20854249:=ck! part 24 1 1337723 xHa20
private theorem xHa22:sumN part 26=22190756:=ck! part 25 1 1336507 xHa21
private theorem xHa23:sumN part 27=23524488:=ck! part 26 1 1333732 xHa22
private theorem low_rows :sumN part 27=23524488 :=xHa23
private theorem high_eq (q:ℕ) (hq:27≤q) :
    part q=(728-2*q)*1924+33306:= by
  change (728-2*q)*mass box (min q 27) 0 +
    sumN (fun d=>mass box (min q 27) (d+1)) (min q 27)= _
  rw [min_eq_right hq]
  have h0:mass box 27 0=1924 :=rfl
  have hs :sumN (fun d=>mass box 27 (d+1)) 27=33306:=rfl
  rw [h0,hs]
private theorem high_rows :sumN (fun i=>part (27+i)) 61=74093162 := by
  have h (i:ℕ) :part (27+i)=(728-2*(27+i))*1924+33306 :=
    high_eq _ (Nat.le_add_right _ _)
  simp only [h]
  rfl
private theorem part_rows :sumN part 88=97617650 :=
  checked low_rows high_rows
theorem budget_cost :
    sumN (fun q=>fullCost box Bank.cheap.U q+partCost box Bank.cheap.U q) (box.b+1) ≤
      oneDebit .cheap:= by
  change sumN (fun q=>full q+part q) 88≤0x26d0cb48
  rw [sum_add,full_rows,part_rows]
end qmb8rCe
end
section
set_option autoImplicit true
namespace qXzfTzc
theorem proof :q0Nj7Rb.c6:= by
  open qmb8rCe in
  exact (window_le_cost box _ (fun q d h hq _ _=>rank_le box q d h hq)).trans budget_cost
end qXzfTzc
end
section
set_option autoImplicit true
namespace qyBUzcc
theorem proof :q1yhP8b.c2 :=
  qXzfTzc.proof
end qyBUzcc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qA2HeGc
noncomputable section
open Polynomial Finset
open P6 (K p)
open P6_7 (RectTail)
open P5 (blockLength)
open P6_7_2 (Input Bs)
open P6_7_2_3 (marks sectionMass rankPrice oldAgreement)
open TD (FP)
open aR (af extend embed)
open oR (qg)
open gT (tK FW)
open pI (abM d2l)
open private c3F from ProximityPrize.SubmissionLower.U
open qkOaTje (cover ordinatePrice mixedPrice phi phi_nonneg price_regular)
open scoped Classical BigOperators
local notation "Dmax" => P6_7_2_3.degree
abbrev lambdaD (b:RectTail) :ℚ:=((blockLength:ℚ)/oldAgreement)*Dmax b
abbrev mu (b:RectTail) :ℚ:=((blockLength - Dmax b:ℕ) :ℚ)/(oldAgreement - Dmax b:ℕ)
private theorem regular_price {r :RectTail} (x :Input r) {T:Finset K} (hT:T⊆x.Γ)
    (f :af 2) (hf :Irreducible f) (hj:0<f.degreeOf 1)
    (hreg : ∀ γ∈T,qg 1 f (extend (x.F.scalar γ))) :
    let b:ℚ:=f.totalDegree
    let j:ℚ:=f.degreeOf 1
    (T.card:ℚ)≤lambdaD r*(4*b*j-2*j*j)+mu r*j+1 :=
  qkOaTje.regular_price' (D:=Dmax r) (Nat.le_add_right _ _) (by cases r <;> decide) (by decide)
    x.F (fun γ hγ=> by
      apply (P6_7.aic x.F hγ).trans
      have hhi:r.kA.hi≤(Bs r).hi:= by cases r <;> decide
      have hh:x.h≤ r.kA.hi:=Int.toNat_le_toNat x.kA.2
      exact Nat.add_le_add_left (hh.trans hhi) _) hT f hf hj hreg
private theorem equation_price {r :RectTail} (x :Input r) {T:Finset K} (hT:T⊆x.Γ)
    {b j:ℕ} {B J:ℚ} (hbB: (b:ℚ)≤B) (hjJ: (j:ℚ)≤J)
    (hp:b<p) (G:tK) (hG:abM G b j)
    (hroot : ∀ γ∈T,FW G (x.F.scalar γ)=0) :
    (T.card:ℚ)≤ordinatePrice (lambdaD r) (mu r) B*j+(mixedPrice (lambdaD r) B (min J B)+B+1)*b:= by
  classical
  obtain ⟨q,hq,hb,hj,hsolve⟩:=bz3.cFG G hG.1 hG.2.1 hG.2.2
  obtain ⟨A,R,hA,hAb,hAj,hR,hRd,hcover⟩:=cover q hq hp hb hj
  let s (γ:K) :=extend (x.F.scalar γ)
  let iy :=T.filter fun γ=>R.eval (s γ)=0
  let reg (f :af 2) :=T.filter fun γ=>qg 1 f (s γ)
  have hord:iy.card≤b^2 := by
    have hi:Set.InjOn s (iy :Set K) := fun _ ha _ hb he =>
      x.F.distinct (hT (filter_subset _ _ ha)) (hT (filter_subset _ _ hb))
        (Polynomial.map_injective embed embed.injective he)
    have hc: (iy.image s).card≤R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (mem_filter.mp hγ).2
    rw [card_image_of_injOn hi] at hc
    exact hc.trans hRd
  have hsub:T⊆iy∪A.biUnion reg:= by
    intro γ hγ
    rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨f,hf,hr⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hr⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨hγ,hr⟩⟩)
  have hall: (T.card:ℚ)≤ iy.card + ∑ f∈A,((reg f).card:ℚ) := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
  have hnum :A.card≤b:= calc
    A.card = ∑ _∈A,1 := by simp
    _ ≤ ∑ f∈A,f.totalDegree :=sum_le_sum fun f hf =>
      (hA f hf).2.trans_le (f.degreeOf_le_totalDegree 1)
    _≤b:=hAb
  let u:=ordinatePrice (lambdaD r) (mu r) B
  let v :=mixedPrice (lambdaD r) B (min J B)
  have hL:0≤lambdaD r := by unfold lambdaD; positivity
  have hB:=(Nat.cast_nonneg b).trans hbB
  have hu:0≤u:= by unfold u ordinatePrice mu; positivity
  have hv :0≤v := by
    have :=phi_nonneg (le_min ((Nat.cast_nonneg j).trans hjJ) hB) (min_le_right J B)
    unfold v mixedPrice
    positivity
  have hreg: (∑ f∈A,((reg f).card:ℚ))≤u*j+v*b+b:= by
    calc
      _ ≤ ∑ f∈A,(u*f.degreeOf 1+v*f.totalDegree+1) := by
        apply sum_le_sum
        intro f hf
        have hfb: (f.totalDegree :ℚ)≤B :=
          (Nat.cast_le.mpr ((single_le_sum (fun g _=>Nat.zero_le g.totalDegree) hf).trans hAb)).trans hbB
        have hfj: (f.degreeOf 1 :ℚ)≤J :=
          (Nat.cast_le.mpr ((single_le_sum (fun g _=>Nat.zero_le (g.degreeOf 1)) hf).trans hAj)).trans hjJ
        have hjb: (f.degreeOf 1 :ℚ)≤f.totalDegree :=Nat.cast_le.mpr (f.degreeOf_le_totalDegree 1)
        exact price_regular hL (Nat.cast_nonneg _) hjb hfb (le_min hfj (hjb.trans hfb)) (min_le_right J B)
          (regular_price x ((filter_subset _ _).trans hT) f (hA f hf).1 (hA f hf).2
            (fun _ hγ=>(mem_filter.mp hγ).2))
      _≤_:= by
        simp only [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_one]
        have hjQ: (∑ f∈A,(f.degreeOf 1 :ℚ))≤j:= by exact_mod_cast hAj
        have hbQ: (∑ f∈A,(f.totalDegree :ℚ))≤b:= by exact_mod_cast hAb
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hjQ hu)
          (mul_le_mul_of_nonneg_left hbQ hv)) (Nat.cast_le.mpr hnum)
  have hordQ: (iy.card:ℚ)≤(b:ℚ)^2 := by exact_mod_cast hord
  have hreserve : (b:ℚ)^2≤B*b:= by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hbB (Nat.cast_nonneg _)
  change (T.card:ℚ)≤u*j+(v+B+1)*b
  linarith only [hall,hreg,hordQ,hreserve]
theorem proof :P6_7_2_3.c3:= by
  classical
  intro b x o Q ha hn hfit
  obtain ⟨G,hG,hGon⟩:=c3F bzS.proof cy5.proof ha hn
  have h:=equation_price x (T:=marks x Q) (filter_subset _ _) (hfit 2) (hfit 1) ha.mixed_lt G hG
    (fun γ (hγ:γ∈marks x Q)=> by
      have hz :=RingHom.mem_ker.mp ((mem_filter.mp hγ).2 hGon)
      simpa only [d2l] using hz)
  simpa [FP,Fin.sum_univ_succ,rankPrice,sectionMass,ordinatePrice,mixedPrice,phi,lambdaD,mu,
    P5.blockLength,mul_assoc] using h
end
end qA2HeGc
end
section
set_option autoImplicit true
namespace qVWQWJa
noncomputable section
open P6_7 (RectTail)

open P6_7_2_3
open TD (GM FP arC)
open scoped BigOperators
private def digit (w n i:ℕ) :ℕ:=(n >>> (w*i)) % 2^w
private def freeCode :RectTail→ℕ
  | .pruned=>0x241e00000121b000000904000000481c00000240c00000121400000090f000000482800000241400000120800000090b000000380d55f57241400000120a0000009048000004824000002420000001205000000902800000481400000241000000120d000000902800000481000000240800000121200000072127ba1bc82400000241000000120700000090a8000003c68edc6e241400000120a000000904000000484000000243a000001208000000904000000481c00000242400000121c000000904800000482400000241000000121000000087d0a485bc8200000024100000012070000009080000004868000002410000001208000000903800000485800000209c437a9b20b000000905800000482400000195ef48a6aa1bd54188908800000484800000241c0000012120000006b3b2df93c838000002422000001218000000
  | .tailOne=>0x2420000001219000000904800000482000000241000000121500000090e000000482c00000241600000120900000090b000000487c00000241600000120b000000905000000482800000241e000001206000000903000000481800000241200000120d000000903000000481800000240a00000121200000090f800000482800000241200000120900000090a800000487800000241600000120b0000009048000004844000002436000001209000000904800000482000000242600000121a000000905000000482800000241200000121100000090e80000048240000024120000012080000009088000004860000002412000001209000000904000000485800000243a00000120c0000009060000004828000002254225ef2dde5969d0908000000484400000241a0000012130000008cd0483b0483c000002422000001219000000
  | .tailTwo=>0x2422000001218000000904800000482400000241000000121500000090d000000482c00000241600000120a00000090b800000487800000241800000120c000000905000000482c00000241e000001207000000903800000481c00000241400000120c000000903800000481800000240c00000121300000090e800000482c00000241400000120900000090b000000487400000241800000120b000000905000000484400000243200000120a0000009050000004824000002426000001219000000905800000482800000241200000121200000090d8000004828000002414000001209000000908800000485c00000241400000120a000000904800000485c00000243800000120c000000906000000482800000243c0000011870a6610908000000484000000241a00000121300000090f0000004840000002424000001219000000
  | .tailThree=>0x2422000001217000000905000000482800000241200000121500000090c800000483000000241800000120a00000090b800000487000000241800000120c000000905800000483000000241e000001208000000904000000481c00000241400000120d000000903800000481c00000240e00000121400000090e000000482c00000241600000120a00000090b000000486c00000241800000120c000000905800000484800000243000000120b0000009050000004824000002426000001218000000905800000482c00000241400000121200000090d000000482c00000241400000120a000000909000000485800000241600000120a000000904800000485c00000243600000120d000000906800000482c00000243800000121f000000908000000484000000241a00000121300000090e8000004840000002424000001219000000
private def terminalCode :RectTail→ℕ
  | .pruned=>0x2795550a3070e0000013d89528cf30100000026cbcadbd5ffec0000040016d48d01f73392ffc004547344aaa5146303c368e9c0a260000002763b0d511dbc40000052cda48b21ea40000008000f50fdcc5eb2b926d184da06022300000020006731f5fa5641da820009479bbcd3cf1c918000c537dc470b052d20004a94694f1ae59745
  | .tailOne=>0x2289eb2905fd800000136d4d2d975f700000025dd7f6674c2400000040012e51074743882bc80039480337d6590822b5a0a2e7301b4000002683cadf0c96b800000502c4a9b356ff800000a18b9f2f175e40000014809823ff7d5a00000200056b798f91e78d3360007b878b3add6ec1a8000b745f0128b91a678003d96c1e608fbec23
  | .tailTwo=>0x2570eb174e85c0000013abf5aacd7dd400000266c00e01cd578000004001514bedb8a345836400408780ba86526fcdb9c412b808ddc000002707a4d92e44500000051bed1919c189000000a4b5871bc71ee0000014e06621b6ad3a000002000613416fe4e49e02c0008b7ec8852508e65c000d92383591a612fa0004455582a2ce9868d
  | .tailThree=>0x2bfb62ef5e5780000014952ee38279d80000027ce9550533050000004001c4409d5562e17f940056e65eff14487a1bc43d62573525c0000028a613ca2cf234000005545547c1539b800000800138ea432e69c7a21dbaeedd05e2dc0000020007eacb4860e073354000c2681634944e0b040015cdda30f7849e3b8005c121d0fd6cd2d73
private def residualCode :RectTail→ℕ
  | .pruned=>0xe2c7864005ebb52ead40f904056086f26664a68420000b0df7878074102d078811103eacd6f29314416b8c00009c952078082863cddf0125a22d4ab54e567816ac7000004cb5a8803873eea618069eb7e7734901372043dc000004cb5a8802cbe58eb9c053f33b069671ffc7458160000a88658e8076bba548a8114d2637d77300cd7a8ddc0000aa04fe58078f2a05bfc117fac50f8735bd33d975e0000d7968fa0063012f40880fd7084571afd601c0360c000004cb5a8806876939c700c3ffffd0210b657bc25580000e970277005c307a6b740f6622e5874ebde9d99301000004cb5a8804d76ef53e409157ed9ae4c60c13f9459000004cb5a8805d82532b700af727ae48aef426aa2687000004cb5a8807682900ae40de5b05997b2f7a37bea2a000000312fd80398d52613801836418ffc190e2f4af69
  | .tailOne=>0xedfe91d007feadc42f413293003bfd2004942ff2f0000bce9760809d138ea67415b600e3b0961ac0c6078f0000a1a93dd80b07f2a76d4178148163518d66182fb070000003086e004be06012f408e22aea250aad7bf0432f00000030843003c012ca2d80706a9b1de8871b10d4eac0000b8c3a8a80a00843b4bc15fbe896a696853d89cca90000b390bed00a3bcb7798c165386b0e6d70ab603732d0000dee29d38085af8ec7b0139203ec0592d01809667a0000e7264e2008287d82da41358ad856a525e6dc0e00b0000f830fc6807c0645b6a812e271353011740aaaeff00000003099b00684ad49a140c359e5ce9cead2de5e91700000030a72007e1b3f92400ec34d7e8ad1bf0b667a2e0000002e2ce0096559fa2c811995817f7d527df221c18000000309f10039c7e448a801b40cb3d061849be37088
  | .tailTwo=>0x101fe4dd00784998387c1232edf4bc8f5bd7a1f5440000ca677e980937802a2f4147e60153692d451e30c8c0000b1010f300a591b2da441635076f0d9523f79ac3bc0000003089900470907edd8085116ed7a0911ee91c9c80000003086e003823211c280692c653a9072af54801f80000c705c088095e0efde8414b8c6f9a29323176a717c0000c1c2e770099a0bacc5c1513a33894939da43b38640000f48df1b007d6afa46941295c4d6ef90038a482dec0000fcf310c007a36882a8412580693138f9ac84f857c00010cd238280742767f06011e34b9df80ed4ba8aed800000003099b00619e2979480b6d995e7f0c76d66595d800000030a9d0075e0128f500dcca1f44b0f0cfea4221000000030bca00867c0db1380fbe5b94eb112be7763968000000309f10037eb53606c019ef813846149ba54d312
  | .tailThree=>0xe847cfb004f02aa85080dc464a84c4c4c23e780da0000c19f295005dc49061a80ebe0c5e544e9825043cb20000a4ec3dc006a0ddc6ce80f9f43a83ad081b05a8fe2000000308c4002e759e668005707e6b4e873b28584ebc0000003086e0024a3437cd0044a62f7e385b3d0aee2a80000b43243a0062e48c1e380f14bf887e4f645890e50e0000b6b48e10061ef5e6bf00f048bddb48f3e2f8225e00000e0ac7960051ea09bdc00df5848c208cbfd7516eec000000309f10053c7fd694009ce9584788d0a3b27480c0000f21a195004ca391b0380dae3fec30cbeda652708e000000309c6004061631e60078953b2dd0a05367c29c400000030a9d004a65b9d71008b56eb2040b9455ba6a1800000030b74004ea12085a809343a278ecc3cf57e13b2000000309f10034105c7128015b935e8fa11715a3efb6
def freeSeedN (b:RectTail) (o:Origin) (i:FreeTest) :ℕ :=
  38740117+digit 37 (freeCode b) (5*o.val+i.val) % 2^24
def freeHeightN (b:RectTail) (o:Origin) (i:FreeTest) :ℕ :=
  digit 37 (freeCode b) (5*o.val+i.val) >>> 24
def terminalZNT (b:RectTail) (o:Origin) :ℕ :=
  digit 75 (terminalCode b) o.val % 2^25
def terminalSeedN (b:RectTail) (o:Origin) :ℕ :=
  (digit 75 (terminalCode b) o.val >>> 25) % 2^29
def terminalHeightN (b:RectTail) (o:Origin) :ℕ :=
  digit 75 (terminalCode b) o.val >>> 54
def bgt (b:RectTail) :Rates b where
  freeSeed o i:=freeSeedN b o i
  freeHeight o i:=freeHeightN b o i
  terminalZ o:=terminalZNT b o
  terminalT o:=terminalSeedN b o
  terminalHeight o:=terminalHeightN b o
def residueN (b:RectTail) (o:Origin) (k :Fin 4) :ℕ :=
  digit 45 (residualCode b) (4*o.val+k.val)
def residue (b:RectTail) (o:Origin) :GM:= fun k=>residueN b o k
private def terminalDualZero:RectTail→Fin 4→ℕ
  | .pruned => ![0x886630392e8,0x2f337d99e0,0x16aa8db57,9651542]
  | .tailOne => ![0xa784e6c7c00,0x4228c784d9,0x6da054a38,0]
  | .tailTwo => ![0x8e77a86cb5e,0x3dcb902425,0x5f9e607e1,0]
  | .tailThree => ![0x703618bed1c,0x25e648f791,0,0]
def terminalDualN (b:RectTail) (o:Origin) (k :Fin 4) :ℕ :=
  if o=0 then terminalDualZero b k else
    if o=8 then
      match b with
      | .pruned => ![0,0,0,9651565] k
      | _=>0
    else 0
def terminalDual (b:RectTail) (o:Origin) :GM:= fun k=>terminalDualN b o k
def a3D (b:RectTail) (o:Origin) (s :bAL) :GM :=
  fun k=>residue b o k+if s=terminalStop then terminalDual b o k else 0
def unitN (b:RectTail) (o:Origin) (j:Fin 3) :ℕ :=
  ∑ k,residueN b o k * arC (originShape b o) k j
def iL (b:RectTail) :ℕ→Fin 3→ℕ
  | 0,_=>0
  | n+1,j=>max (iL b n j) (if h:n<14 then unitN b ⟨n,h⟩ j else 0)
def a4Q (b:RectTail) (o:Origin) (j:Fin 3) :ℕ :=
  iL b (o.val+1) j - iL b o.val j
def factorBook (b:RectTail) :ℕ := ∑ o:Origin,∑ j:Fin 3,a4Q b o j*introCap b o j
def terminalBook (b:RectTail) :ℚ := ∑ o:Origin,FP (terminalDual b o) (endCap b o)
end
end qVWQWJa
end
