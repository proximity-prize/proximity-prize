import ProximityPrize.SubmissionLower.Z9Zvicc
import ProximityPrize.SubmissionLower.ZeFzsob
set_option Elab.async false
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace qFOgTpd
noncomputable section
open Finset
open P6 (K p)
open P6_7_3 (Input IntroIndex introCap)
open cu (Jet)
open gT (Ambient IZ gk iJ)
open pI (xN oU dM pN mass a5I F7)
open YX (bQz bjf eHX evL)

open qQ (VN a4N bH5 bH6 bH4
  aJr bNe)
open akZ (ajz btm bKa caQ cfi)
open scoped Classical
open private a8m bYs ddo from ProximityPrize.SubmissionLower.CR
open private b6z from ProximityPrize.SubmissionLower.D7
structure Parents (x :Input) (D:Finset Jet) (cut:Jet→Jet) where
  parents :Jet→Finset (Ideal Ambient)
  gH :Finset K
  paid_bound:gH.card≤projectionFee
  geometric : ∀ f∈D,∀ q∈parents f,
    xN q∧q.height=2∧iJ f∈q∧iJ (cut f)∈q
  disjoint : ∀ f∈D,∀ g∈D,f≠g→Disjoint (parents f) (parents g)
  Eh : ∀ f∈D,∀ γ∈x.Γ,Mark x f γ→Mark x (cut f) γ →
    γ∈gH ∨ ∃ g∈D,∃ q∈parents g,IZ q (x.M.label γ) (x.F.scalar γ)
theorem geometric_cover (x :Input) (D:Finset Jet) (origin :Jet→ IntroIndex)
    (cut:Jet→Jet) (hirr : ∀ f∈D,Irreducible f) (hcut : ∀ f∈D,¬ f∣cut f)
    (hcaps : ∀ f∈D,oU (cut f) (box (origin f)))
    (nest : ∀ i≤last,∀ j,ajz (D.filter (fun f=>i≤(origin f).val)) j≤ introCap i j) :
    Nonempty (Parents x D cut) := by
  have each (f :Jet) (hf :f∈D) :
      ∃ S:Finset (Ideal Ambient),bQz f (cut f) S ∧
        (∀ q∈S,q.height=2∧bjf q) ∧
        dM S (fun k=>akZ.aHP (box (origin f)) k f) ∧
        ∀ γ∈x.Γ,Mark x f γ→Mark x (cut f) γ →
          ∃ q∈S,IZ q (x.M.label γ) (x.F.scalar γ) := by
    have hp:=b6z (hirr f hf) (hcut f hf)
    obtain ⟨S,hs,hcover⟩:=aRY.proof _ _ hp
    obtain ⟨hfinite,hfit⟩:=a8m _ _ hp (btm f) (box (origin f))
      (caQ (hirr f hf).ne_zero) (box_J _) (bKa f) (hcaps f hf) S hs
    refine ⟨S,hs,?_,fun k=>(hfit k).trans_eq (cfi _ _ (box_J _) k),
      fun γ _=>hcover (x.M.label γ) (x.F.scalar γ)⟩
    intro q hq
    obtain ⟨hprime,hd,hrow,hg⟩:=hs q hq
    exact ⟨bYs hp hprime hd hrow hg,hfinite q hq⟩
  let S (f :Jet) :=if h:f∈D then Classical.choose (each f h) else ∅
  have hs (f :Jet) (hf :f∈D) :=Classical.choose_spec (each f hf)
  have hS (f :Jet) (hf :f∈D) :
      S f=Classical.choose (each f hf) :=dite_eq_left hf
  let all:=D.biUnion S
  have hmass :dM all massCap:= fun k=> calc
    _ ≤ ∑ f∈D,mass (S f) k :=pI.bhF _ _ _
    _ ≤ ∑ f∈D,akZ.aHP (box (origin f)) k f :=
      sum_le_sum fun f hf=> by rw [hS f hf]; exact (hs f hf).2.2.1 k
    _≤_:=charge D origin nest k
  have geom (q:Ideal Ambient) (hq:q∈all) :
      q.IsPrime∧ringKrullDim (gk q)=2∧q.height=2∧bjf q:= by
    obtain ⟨f,hf,hq⟩:=mem_biUnion.mp hq
    rw [hS f hf] at hq
    exact ⟨((hs f hf).1 q hq).1,((hs f hf).1 q hq).2.1,(hs f hf).2.1 q hq⟩
  let Kw:=all.filter fun q=>pN q 0=0
  have seedExists (q:Ideal Ambient) (hq:q∈Kw) :
      ∃ C:VN,C.curve.totalDegree≤pN q 2 ∧
        C.points.card≤pN q 3 ∧ ∀ z R,IZ q z R→C.ow z := by
    obtain ⟨hq,hz⟩:=mem_filter.mp hq
    obtain ⟨hprime,hd,_,hf⟩:=geom q hq
    exact ddo q hprime hd hf hz
  let images (q:Ideal Ambient) :VN :=
    if h:q∈Kw then Classical.choose (seedExists q h) else ⟨1,one_ne_zero,∅⟩
  have hi (q:Ideal Ambient) (hq:q∈Kw) :
      (images q).curve.totalDegree≤pN q 2 ∧
      (images q).points.card≤pN q 3 ∧ ∀ z R,IZ q z R→(images q).ow z := by
    simpa only [images,dite_eq_left hq] using Classical.choose_spec (seedExists q hq)
  let cover :=a4N Kw images
  have hc:=(bH5 Kw images).trans
    ((sum_le_sum fun q hq=>(hi q hq).1).trans
      ((a5I (filter_subset _ _) 2).trans (hmass 2)))
  have hp:=(bH6 Kw images).trans
    ((sum_le_sum fun q hq=>(hi q hq).2.1).trans
      ((a5I (filter_subset _ _) 3).trans (hmass 3)))
  let seedPaid :=x.Γ.filter fun γ=>cover.ow (x.M.label γ)
  have hseed :seedPaid.card≤(p+1)*massCap 2+massCap 3 :=
    (aJr (T:=seedPaid) (fun _ _ _ _ h=>sub_left_inj.mp h) cover
      (hc.trans_lt (mass_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)).trans
      (Nat.add_le_add (Nat.mul_le_mul_left _ hc) hp)
  let dominant (q:Ideal Ambient) :=Function.Injective ((Ideal.Quotient.mk q).comp F7)
  let ord:=all.filter fun q=>0<pN q 0 ∧ ¬ dominant q
  let marks (q:Ideal Ambient) :=x.Γ.filter fun γ=>IZ q (x.M.label γ) (x.F.scalar γ)
  let ordPaid :=ord.biUnion marks
  have hord:ordPaid.card≤ massCap 0:= by
    refine (card_biUnion_le.trans (sum_le_sum ?_)).trans
      ((a5I (filter_subset _ _) 0).trans (hmass 0))
    intro q hq
    obtain ⟨hq,hpos,hno⟩:=mem_filter.mp hq
    refine (card_le_one.mpr fun y hy z hz => ?_).trans hpos
    obtain ⟨hy,hm⟩:=mem_filter.mp hy
    obtain ⟨hz,hn⟩:=mem_filter.mp hz
    exact x.F.distinct hy hz (bNe (eHX (geom q hq).1 hno hm hn))
  let owner (q:Ideal Ambient) :=if h:q∈all then Classical.choose (mem_biUnion.mp h) else 0
  have owns (q:Ideal Ambient) (h:q∈all) :owner q∈D ∧q∈S (owner q) := by
    simpa only [owner,dite_eq_left h] using Classical.choose_spec (mem_biUnion.mp h)
  let Bp (f :Jet) :=(S f).filter fun q =>
    owner q=f∧0<pN q 0∧dominant q
  refine ⟨⟨Bp,seedPaid∪ordPaid,(card_union_le _ _).trans
    ((Nat.add_le_add hseed hord).trans (by decide)),?_,?_,?_⟩⟩
  · intro f hf q hq
    obtain ⟨hq,_,hpos,hdom⟩:=mem_filter.mp hq
    have hall:q∈all:=mem_biUnion.mpr ⟨f,hf,hq⟩
    obtain ⟨hprime,hd,hh,hfinite⟩:=geom q hall
    have hlim (k :Fin 4) :pN q k<p :=
      ((evL hall k).trans (hmass k)).trans_lt (mass_small k)
    have hmem:=(hs f hf).1 q (hS f hf ▸ hq)
    exact ⟨⟨hprime,hd,hfinite.Kw,hfinite.jU,hfinite.kK,hfinite.Bo,
      ⟨hpos,hlim 0⟩,hlim 2,hlim 3,hdom⟩,hh,hmem.2.2⟩
  · intro f _ g _ hne
    exact disjoint_left.mpr fun q hf hg=>hne ((mem_filter.mp hf).2.1.symm.trans (mem_filter.mp hg).2.1)
  · intro f hf γ hγ hz hw
    obtain ⟨q,hq,hmark⟩:=(hs f hf).2.2.2 γ hγ hz hw
    have hall:q∈all:=mem_biUnion.mpr ⟨f,hf,(hS f hf).symm ▸ hq⟩
    by_cases hzero :pN q 0=0
    · have hmem:q∈Kw:=mem_filter.mpr ⟨hall,hzero⟩
      exact Or.inl (mem_union_left _ (mem_filter.mpr
        ⟨hγ,bH4 hmem ((hi q hmem).2.2 _ _ hmark)⟩))
    · have hpos :=Nat.pos_of_ne_zero hzero
      by_cases hdom:dominant q
      · obtain ⟨hg,hq⟩:=owns q hall
        exact Or.inr ⟨owner q,hg,q,mem_filter.mpr ⟨hq,rfl,hpos,hdom⟩,hmark⟩
      · exact Or.inl (mem_union_right _ (mem_biUnion.mpr
          ⟨q,mem_filter.mpr ⟨hall,hpos,hdom⟩,mem_filter.mpr ⟨hγ,hmark⟩⟩))
end
end qFOgTpd
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace qFOgTpd
noncomputable section
open Finset
open P6 (K)
open P6_7_3
open cu (Jet)
open DP (U4)

open pI (oU)
open akZ (strip aRJ ajz cN5 cVg)
open scoped Classical
def c1 :Prop :=
  ∀ (x :Input) (G:Jet) (D:Finset Jet),aRJ G D →
    (∀ f∈D,f.natDegree=0)→(∀ j,ajz D j≤ introCap last j) →
    ∃ gH :Finset K,gH.card≤eHB ∧
      ∀ f∈D,∀ γ∈x.Γ,Mark x f γ→γ∈gH
def c2 :Prop :=
  ∀ (x :Input) (P:Poles x) (R:Reference x P) (_top:TopPair x) (D:Finset Jet),
    aRJ (U4 R.raw) D →
    (∀ f∈D,0<f.natDegree)→(∀ j,ajz D j≤ introCap last j) →
    ∃ gH :Finset K,gH.card≤akj ∧
      ∀ f∈D,Nonempty (LastCut x gH f)
def c3:Prop :=
  ∀ (x :Input) (f :Jet) (g:LineRow),0<wD f 1→0<wD f 2 →
    (∀ j,wD f j≤ introCap last j)→LineCaps f g →
    (x.Γ.filter (LineRoot x g)).card≤lineFee (wD f 0) (wD f 1) (wD f 2)
private theorem gX {A B:Finset K} {a b:ℕ} (ha :A.card≤a) (hb:B.card≤b) :
    (A∪B).card≤a+b :=
  (card_union_le _ _).trans (Nat.add_le_add ha hb)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_7_3.c4 := by
  intro x P pick top
  obtain ⟨A⟩:=bRI.proof _ _ (pick.main ⟨0,by decide⟩).free_ne (anchor_caps pick)
  obtain ⟨a⟩:=strip (pick.main ⟨0,by decide⟩).free_ne (anchor_caps pick) A
  obtain ⟨fixed,hfixed,hfa⟩:=anchor_book x a
  obtain ⟨D,hD,hcap,hroot⟩:=cVg a
  obtain ⟨R,⟨C⟩⟩:=schedule pick hD hcap
  let O:=D.filter fun f=>(C.origin f).val=last∧f.natDegree=0
  let F:=D.filter fun f=>(C.origin f).val=last∧0<f.natDegree
  let T:=D \ O
  have suffix (E :Finset Jet) (hs :E⊆D.filter (fun f=>last≤(C.origin f).val)) (j:Fin 3) :
      ajz E j≤ introCap last j:=(cN5 hs j).trans (C.nested last le_rfl j)
  have hO:O⊆D.filter (fun f=>last≤(C.origin f).val) := fun _ hf =>
    let h:=mem_filter.mp hf
    mem_filter.mpr ⟨h.1,h.2.1.ge⟩
  have hF:F⊆D.filter (fun f=>last≤(C.origin f).val) := fun _ hf =>
    let h:=mem_filter.mp hf
    mem_filter.mpr ⟨h.1,h.2.1.ge⟩
  obtain ⟨iy,hordinary,hOrd⟩ :=
    h1 x (anchorRow pick) O (hD.mono (filter_subset _ _)) (fun _ hf=>(mem_filter.mp hf).2.2) (suffix O hO)
  have href :aRJ (U4 R.raw) F:= by
    refine ⟨?_,hD.pairwise.mono (filter_subset _ _)⟩
    intro f hf
    obtain ⟨hm,he,_⟩:=mem_filter.mp hf
    obtain ⟨hi,_,hu,hs,hr⟩:=hD.factors f hm
    exact ⟨hi,C.last_dvd f hm he,hu,hs,hr⟩
  obtain ⟨singular,hsing,cuts⟩:=h2 x P R top F href
    (fun _ hf=>(mem_filter.mp hf).2.2) (suffix F hF)
  let be1 (f :Jet) (hf :f∈F) :=Classical.choice (cuts f hf)
  let cut (f :Jet) :=if h: (C.origin f).val<last then C.cut ⟨_,h⟩
    else if hf :f∈F then (be1 f hf).cut else 0
  let line (f :Jet) :=if hf :f∈F then (be1 f hf).line else false
  let lines (f :Jet) :=if hf :f∈F then
    if (be1 f hf).line then x.Γ.filter (LineRoot x (be1 f hf).row) else ∅ else ∅
  have hT:T⊆D:=sdiff_subset
  have early_no (f :Jet) (h: (C.origin f).val<last) :f∉F :=
    fun hf=>h.ne (mem_filter.mp hf).2.1
  have late_mem (f :Jet) (hf :f∈T) (h : ¬ (C.origin f).val<last) :f∈F:= by
    have he : (C.origin f).val=last :=le_antisymm (Nat.le_of_lt_succ (C.origin f).isLt) (Nat.le_of_not_gt h)
    refine mem_filter.mpr ⟨hT hf,he,Nat.pos_of_ne_zero ?_⟩
    intro hz
    exact (mem_sdiff.mp hf).2 (mem_filter.mpr ⟨hT hf,he,hz⟩)
  have individual (f :Jet) (hf :f∈F) (j:Fin 3) :wD f j≤ introCap last j :=
    (single_le_sum (f := fun g=>wD g j) (fun _ _=>Nat.zero_le _) hf).trans (suffix F hF j)
  have proper (f :Jet) (hf :f∈T) : ¬ f∣cut f := by
    by_cases he : (C.origin f).val<last
    · simpa only [cut,dite_eq_left he] using C.proper f (hT hf) ⟨_,he⟩ rfl
    · have hl:=late_mem f hf he
      simpa only [cut,dite_eq_right he,dite_eq_left hl] using (be1 f hl).proper
  have caps (f :Jet) (hf :f∈T) :oU (cut f) (box (C.origin f)) := by
    by_cases he : (C.origin f).val<last
    · simp only [cut,box,dite_eq_left he]
      exact C.caps ⟨_,he⟩
    · have hl:=late_mem f hf he
      simp only [cut,box,dite_eq_right he,dite_eq_left hl]
      exact enclose_last (individual f hl) _ (be1 f hl).caps
  have nest (i) (hi:i≤last) (j) :
      ajz (T.filter (fun f=>i≤(C.origin f).val)) j≤ introCap i j :=
    (cN5 (filter_subset_filter _ hT) j).trans (C.nested i hi j)
  obtain ⟨G⟩:=geometric_cover x T C.origin cut (fun f hf=>(hD.factors f (hT hf)).1) proper caps nest
  let gH :=fixed∪iy∪singular∪G.gH
  refine ⟨⟨T,C.origin,cut,line,lines,G.parents,gH,?_,nest,?_,?_,?_,?_,?_,
    G.geometric,G.disjoint,?_⟩⟩
  · exact (gX (gX (gX hfixed hordinary) hsing) G.paid_bound).trans (by decide)
  · intro f hf
    exact ⟨(hD.factors f (hT hf)).1,(hD.factors f (hT hf)).2.1,proper f hf⟩
  · intro f hf
    by_cases he : (C.origin f).val<last
    · simp only [dite_eq_left he,cut,line,dite_eq_right (early_no f he),true_and]
      exact C.caps ⟨_,he⟩
    · have hl:=late_mem f hf he
      simp only [cut,dite_eq_right he,line,dite_eq_left hl]
      change if (be1 f hl).line then oU (be1 f hl).cut (akZ.btm f)
        else oU (be1 f hl).cut (aOm f)
      cases h: (be1 f hl).line <;>
        simpa only [h,Bool.false_eq_true,ite_false,ite_true] using (be1 f hl).caps
  · intro f _ g _ he eq
    have hg: (C.origin g).val<last :=eq ▸ he
    simp only [cut,dite_eq_left he,dite_eq_left hg]
    have eqv :=congrArg (fun i:IntroIndex=>i.val) eq
    exact congrArg C.cut (Fin.ext eqv)
  · intro f _
    by_cases hf :f∈F
    · cases h: (be1 f hf).line
      · simp [line,lines,hf,h]
      · simpa [line,lines,hf,h] using h3 x f (be1 f hf).row (mem_filter.mp hf).2.2
          ((be1 f hf).line_pos h) (individual f hf) ((be1 f hf).line_caps h)
    · simp [line,lines,hf]
  · intro f _ h
    by_cases hf :f∈F
    · have hh: (be1 f hf).line=true := by simpa only [line,dite_eq_left hf] using h
      exact ⟨(mem_filter.mp hf).2.2,(be1 f hf).line_pos hh⟩
    · simp [line,hf] at h
  · intro γ hγ
    have use (f :Jet) (hf :f∈T) (hrow:Mark x f γ) (hcut:Mark x (cut f) γ) :
        γ∈gH ∨ ∃ g∈T,γ∈lines g ∨ ∃ q∈G.parents g,gT.IZ q (x.M.label γ) (x.F.scalar γ) := by
      rcases G.Eh f hf γ hγ hrow hcut with hp | ⟨g,hg,q,hq,hm⟩
      · exact Or.inl (mem_union_right _ hp)
      · exact Or.inr ⟨g,hg,Or.inr ⟨q,hq,hm⟩⟩
    rcases a.Eh _ _ (anchor_zero pick γ hγ) with hc | ha | hz
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (hfa γ hγ (Or.inl hc)))))
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (hfa γ hγ (Or.inr ha)))))
    obtain ⟨f,hf,hrow⟩:=hroot _ _ hz
    by_cases ho:f∈O
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (hOrd f ho γ hγ hrow))))
    have ht:f∈T:=mem_sdiff.mpr ⟨hf,ho⟩
    by_cases he : (C.origin f).val<last
    · exact use f ht hrow (by simpa only [cut,dite_eq_left he] using C.zero ⟨_,he⟩ γ hγ)
    have hl:=late_mem f ht he
    rcases (be1 f hl).Eh γ hγ hrow with hp | hc | ⟨hline,hm⟩
    · exact Or.inl (mem_union_left _ (mem_union_right _ hp))
    · exact use f ht hrow (by simpa only [cut,dite_eq_right he,dite_eq_left hl] using hc)
    · exact Or.inr ⟨f,ht,Or.inl (by simpa [lines,hl,hline,hγ] using hm)⟩
end
end qFOgTpd
end
