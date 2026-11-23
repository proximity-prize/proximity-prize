import ProximityPrize.SubmissionLower.ZRtoqxb
import ProximityPrize.SubmissionLower.Zyuvo1c
set_option Elab.async false
open _root_ renaming Fin.sum_univ_succ → zCS, Fin.sum_univ_three → zCj, Fin.sum_univ_zero → zDT, Finset → zJe, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.cast_sum → zCt
section
set_option autoImplicit true
set_option maxRecDepth 6000
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace qBPZs8a
noncomputable section
open Finset
open P6 (K)
open P6_7_1
open cu (Jet qD)
open DP (U4)
open gT (FW IZ)
open pI (NO oU)
open akZ (aSK strip aRJ ajz cN5 cVg)
open scoped Classical
def c1 :Prop :=
  ∀ (x :Input) (P:Poles x) (R:EarlyPicks x P)
    (A:NO R.anchorRow anchor) (a :aSK A),
    ∃ gH :zJe K,gH.card≤fixedContentFee ∧
      ∀ γ∈x.Γ,qD (x.M.label γ) a.content=0∨FW A.equation (x.F.scalar γ)=0 →
        γ∈gH
def c2 :Prop :=
  ∀ (x :Input) (G:Jet) (D:zJe Jet),aRJ G D →
    (∀ f∈D,f.natDegree=0)→(∀ j,ajz D j≤ introCap last j) →
    ∃ gH :zJe K,gH.card≤eHB ∧
      ∀ f∈D,∀ γ∈x.Γ,Mark x f γ→γ∈gH
def c3:Prop :=
  ∀ (x :Input) (P:Poles x) (A:Reference x P),TopPair x → ∀ (D:zJe Jet),
    aRJ (U4 A.raw) D→(∀ f∈D,0<f.natDegree) →
    (∀ j,ajz D j≤ introCap last j) →
    ∃ gH :zJe K,gH.card≤akj ∧ ∀ f∈D,Nonempty (LastCut x gH f)
def c4 :Prop :=
  ∀ (x :Input) (f :Jet) (g:LineRow),0<wD f 1→0<wD f 2 →
    (∀ j,wD f j≤ introCap last j)→LineCaps f g →
    (x.Γ.filter (LineRoot x g)).card≤lineFee (wD f 0) (wD f 1) (wD f 2)
private theorem gX {A B:zJe K} {a b:ℕ} (ha :A.card≤a) (hb:B.card≤b) :
    (A∪B).card≤a+b :=
  (card_union_le _ _).trans (Nat.add_le_add ha hb)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_7_1.c3:= by
  intro x P R top
  have hn:=(R.free ⟨0,by decide⟩).ne_zero
  have hc:=anchor_caps R
  obtain ⟨A⟩:=bRI.proof _ _ hn hc
  obtain ⟨a⟩:=strip hn hc A
  obtain ⟨fixed,hfixed,hfa⟩:=h1 x P R A a
  obtain ⟨D,hD,hcap,hroot⟩:=cVg a
  obtain ⟨C⟩:=schedule R hD hcap
  obtain ⟨ref⟩:=reference R
  let O:=D.filter fun f=>(C.origin f).val=last∧f.natDegree=0
  let F:=D.filter fun f=>(C.origin f).val=last∧0<f.natDegree
  let T:=D \ O
  have suffix (E :zJe Jet) (hs :E⊆D.filter (fun f=>last≤(C.origin f).val)) (j:Fin 3) :
      ajz E j≤ introCap last j:=(cN5 hs j).trans (C.nested last le_rfl j)
  have hO:O⊆D.filter (fun f=>last≤(C.origin f).val) := fun _ hf =>
    let h:=mem_filter.mp hf
    mem_filter.mpr ⟨h.1,h.2.1.ge⟩
  have hF:F⊆D.filter (fun f=>last≤(C.origin f).val) := fun _ hf =>
    let h:=mem_filter.mp hf
    mem_filter.mpr ⟨h.1,h.2.1.ge⟩
  obtain ⟨iy,hordinary,hOrd⟩ :=
    h2 x R.anchorRow O (hD.mono (filter_subset _ _)) (fun _ hf=>(mem_filter.mp hf).2.2) (suffix O hO)
  have href :aRJ (U4 ref.raw) F:= by
    refine ⟨?_,hD.pairwise.mono (filter_subset _ _)⟩
    intro f hf
    obtain ⟨hm,he,_⟩:=mem_filter.mp hf
    obtain ⟨hi,_,hu,hs,hr⟩:=hD.factors f hm
    exact ⟨hi,C.survives f referenceIndex (by rw [he]; decide) _
      (Submodule.subset_span ⟨ref.raw,ref.mem,rfl⟩),hu,hs,hr⟩
  obtain ⟨singular,hsing,cuts⟩:=h3 x P ref top F href
    (fun _ hf=>(mem_filter.mp hf).2.2) (suffix F hF)
  let be1 (f :Jet) (hf :f∈F) :=Classical.choice (cuts f hf)
  let cut (f :Jet) :=if h: (C.origin f).val<last then C.cut ⟨_,h⟩
    else if hf :f∈F then (be1 f hf).cut else 0
  let line (f :Jet) :=if hf :f∈F then (be1 f hf).line else false
  let lines (f :Jet) :=if hf :f∈F then
    if (be1 f hf).line then x.Γ.filter (LineRoot x (be1 f hf).row) else ∅ else ∅
  have hT:T⊆D:=sdiff_subset
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
      exact DP.d3r P.crt x.word (C.mem ⟨_,he⟩)
    · have hl:=late_mem f hf he
      simp only [cut,box,dite_eq_right he,dite_eq_left hl]
      exact enclose_last (individual f hl) _ (be1 f hl).caps
  have nest (i) (hi:i≤last) (j) :
      ajz (T.filter (fun f=>i≤(C.origin f).val)) j≤ introCap i j :=
    (cN5 (filter_subset_filter _ hT) j).trans (C.nested i hi j)
  obtain ⟨G⟩:=geometric_cover x T C.origin cut (fun f hf=>(hD.factors f (hT hf)).1) proper caps nest
  let gH :=fixed∪iy∪singular∪G.gH
  refine ⟨({
    factors :=T
    origin :=C.origin
    cut:=cut
    line :=line
    lineMarks :=lines
    parents :=G.parents
    gH :=gH
    paid_bound:=(gX (gX (gX hfixed hordinary) hsing) G.paid_bound).trans (by decide)
    nested:=nest
    survives := fun f _ i=>C.survives f i
    geometric:=G.geometric
    disjoint:=G.disjoint
    proper := ?_
    early_cut := ?_
    shared_cut := ?_
    last_cut := ?_
    line_pos := ?_
    line_bound := ?_
    Eh := ?_ } : OriginCover x P R)⟩
  · intro f hf
    obtain ⟨hi,hd,hu,_,_⟩:=hD.factors f (hT hf)
    exact ⟨hi,hd,hu,proper f hf⟩
  · intro f _ i hi
    have he : (C.origin f).val<last :=hi ▸ i.isLt
    have e : (⟨(C.origin f).val,he⟩:Intro)=i:=Fin.ext hi.symm
    simpa only [cut,dite_eq_left he,e] using And.intro (C.mem i) (C.avoids i)
  · intro f _ g _ he eq
    have hg: (C.origin g).val<last :=eq ▸ he
    simp only [cut,dite_eq_left he,dite_eq_left hg]
    exact congrArg C.cut (Fin.ext (congrArg (fun i:Origin=>i.val) eq))
  · intro f hf h
    have he : ¬ (C.origin f).val<last := by rw [h]; exact Nat.lt_irrefl last
    have hl:=late_mem f hf he
    refine ⟨(mem_filter.mp hl).2.2,?_⟩
    have hown:akZ.btm f=⟨0,wD f 0,wD f 1,wD f 2⟩:=rfl
    simpa only [cut,line,dite_eq_right he,dite_eq_left hl,hown] using (be1 f hl).caps
  · intro f _ h
    by_cases hf :f∈F
    · have hh: (be1 f hf).line=true := by simpa only [line,dite_eq_left hf] using h
      obtain ⟨_,he,hv⟩:=mem_filter.mp hf
      have he' : C.origin f=lastOrigin :=Fin.ext he
      have hn : ¬ (C.origin f).val<last := by rw [he]; exact Nat.lt_irrefl last
      exact ⟨he',hv,(be1 f hf).line_pos hh,
        by simpa only [cut,dite_eq_right hn,dite_eq_left hf] using (be1 f hf).separant hh⟩
    · simp [line,hf] at h
  · intro f _
    by_cases hf :f∈F
    · cases h: (be1 f hf).line
      · simp [line,lines,hf,h]
      · simpa [line,lines,hf,h] using h4 x f (be1 f hf).row (mem_filter.mp hf).2.2
          ((be1 f hf).line_pos h) (individual f hf) ((be1 f hf).line_caps h)
    · simp [line,lines,hf]
  · intro γ hγ
    have use (f :Jet) (hf :f∈T) (hrow:Mark x f γ) (hcut:Mark x (cut f) γ) :
        γ∈gH ∨ ∃ g∈T,γ∈lines g ∨ ∃ q∈G.parents g,IZ q (x.M.label γ) (x.F.scalar γ) := by
      rcases G.Eh f hf γ hγ hrow hcut with hp | ⟨g,hg,q,hq,hm⟩
      · exact Or.inl (mem_union_right _ hp)
      · exact Or.inr ⟨g,hg,Or.inr ⟨q,hq,hm⟩⟩
    have aff :=a.Eh _ _ (anchor_zero R γ hγ)
    rcases or_assoc.mpr aff with h | hz
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (hfa γ hγ h))))
    obtain ⟨f,hf,hrow⟩:=hroot _ _ hz
    by_cases ho:f∈O
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (hOrd f ho γ hγ hrow))))
    have ht:f∈T:=mem_sdiff.mpr ⟨hf,ho⟩
    by_cases he : (C.origin f).val<last
    · let i:Intro:=⟨_,he⟩
      have hz' := necessary P (cutoff_lt (shape i) (intro_positive i)) (C.mem i) hγ
      exact use f ht hrow (by simpa only [cut,dite_eq_left he,Mark,i] using hz')
    have hl:=late_mem f ht he
    rcases (be1 f hl).Eh γ hγ hrow with hp | hcut | ⟨hline,hm⟩
    · exact Or.inl (mem_union_left _ (mem_union_right _ hp))
    · exact use f ht hrow (by simpa only [cut,dite_eq_right he,dite_eq_left hl] using hcut)
    · exact Or.inr ⟨f,ht,Or.inl (by simpa [lines,hl,hline,hγ] using hm)⟩
end
end qBPZs8a
end
section
set_option autoImplicit true
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qrT6Ada
noncomputable section
open Finset q3rjQGe
open P6_7_1 (Origin introCap wD lastOrigin)
open cu (Jet Shape)
open TD (GM FP a3x dYl)
open scoped Classical BigOperators
theorem dot_mixed (w:GM) (v :Fin 3→ℕ) (s :Shape) :
    FP w (kK v s) =
      ∑ j:Fin 3,(∑ k :Fin 4,w k*(mixedCols s k j:ℚ))*(v j:ℚ) := by
  simp only [FP,kK,mul_sum,sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _=>sum_congr rfl fun k _ => ?_
  ring
private theorem crE {α:Type*} (S:zJe α) (w:GM) (v :α→GM) :
    (∑ f∈S,FP w (v f))=FP w (fun k => ∑ f∈S,v f k) := by
  simp only [FP,mul_sum]
  exact sum_comm
private theorem dlP (i:Free) (j:Fin 3) (k :Fin 4) :
    SS j i.castSucc k≤SS j termTrial k := by
  apply (Nat.cast_le (α:=ℚ)).2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide
private theorem aE8 (o:Origin) (s :bAL) (k :Fin 4) :
    stopPrice a b z ar br o s k≤ corePrice o s k+globalRate k := by
  refine Fin.cases ?_ (Fin.lastCases ?_ (fun i => ?_)) s
  · exact le_add_of_nonneg_right
      (add_nonneg (dSz 0 _ _) (dSz 2 _ _))
  · simp only [stopPrice,corePrice,Fin.cases_succ,Fin.lastCases_last,rectPrice,globalRate]
    exact le_of_eq (by ring)
  · simp only [stopPrice,corePrice,Fin.cases_succ,Fin.lastCases_castSucc,
      freePrice,globalRate]
    linarith only [dlP i 0 k,dlP i 2 k]
private theorem global_bound (B:aAU) :
    (∑ f∈B.factors,∑ s :bAL,FP globalRate (B.stops f s))≤globalBook := by
  simp only [crE]
  exact a3x (fun k=>add_nonneg (dSz 0 _ k)
    (dSz 2 _ k)) B.global
private theorem free_bound (B:aAU) :
    (∑ f∈B.factors,∑ s :bAL,FP (freePart (B.origin f) s) (B.stops f s))≤freeBook := by
  have h (f :Jet) : (∑ s :bAL,FP (freePart (B.origin f) s) (B.stops f s)) =
      if B.origin f=0 then FP freeDual (B.stops f termStop) else 0:= by
    by_cases ho:B.origin f=0
    · simp only [freePart,ho,true_and,ite_true]
      rw [sum_eq_single termStop]
      · rw [ite_eq_left rfl]
      · intro s _ hs
        rw [ite_eq_right hs]
        simp [FP]
      · simp
    · simp [freePart,ho,FP]
  simp only [h,← sum_filter,crE]
  exact a3x freeDual_nonneg (B.all_free 0)
private theorem pay_factor (B:aAU) (f :Jet) (hf :f∈B.factors) (hl:Absorbs) :
    lineCharge f (B.line f)+(∑ s :bAL,FP (residual (B.origin f)) (B.stops f s)) ≤
      ∑ j,unit (B.origin f) j*(wD f j:ℚ) := by
  have hh: (∑ s :bAL,FP (residual (B.origin f)) (B.stops f s)) ≤
      FP (residual (B.origin f)) (kK (wD f) (afF (B.origin f) f (B.line f))) := by
    rw [crE]
    exact a3x (fun k=>zqJ (residualN (B.origin f) k)) (B.initial f hf)
  refine (add_le_add le_rfl hh).trans ?_
  cases h:B.line f with
  | false =>
    simpa only [h,lineCharge,afF,Bool.false_eq_true,ite_false,Nat.cast_zero,
      zero_add,unit] using (dot_mixed (residual (B.origin f)) (wD f) (originShape (B.origin f))).le
  | true =>
    obtain ⟨ho,hj,hu⟩:=B.line_ok f hf h
    have hs (j:Fin 3) :wD f j≤ introCap lastOrigin.val j:= by
      have hm:f∈B.factors.filter (fun f=>lastOrigin.val≤(B.origin f).val) :=
        mem_filter.mpr ⟨hf,by rw [ho]⟩
      exact (single_le_sum (fun g _=>Nat.zero_le (wD g j)) hm).trans (B.nested lastOrigin j)
    simpa only [h,ho,lineCharge,afF,ite_true] using hl (wD f) hs (B.spend_order f hf) hj hu
private theorem aNI (B:aAU) (hl:Absorbs) (hc : ∀ o j,unit o j≤ iL o j) :
    (∑ f∈B.factors,(lineCharge f (B.line f) +
      ∑ s :bAL,FP (residual (B.origin f)) (B.stops f s)))≤factorBook := by
  calc
    _ ≤ ∑ f∈B.factors,∑ j,iL (B.origin f) j*(wD f j:ℚ) :=
      sum_le_sum fun f hf=>(pay_factor B f hf hl).trans
        (sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (hc _ _) (zqJ _))
    _ = ∑ j:Fin 3,∑ i:Origin,∑ f∈B.factors,
        (if i≤B.origin f then a4Q i j else 0)*(wD f j:ℚ) := by
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      simp only [iL,sum_mul]
      exact sum_comm
    _ = ∑ i:Origin,∑ j:Fin 3,a4Q i j *
        (∑ f∈B.factors.filter (fun f=>i.val≤(B.origin f).val),(wD f j:ℚ)) := by
      rw [sum_comm]
      simp only [sum_filter,mul_sum]
      refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>sum_congr rfl fun f _ => ?_
      have hi: (i≤B.origin f)=(i.val≤(B.origin f).val) :=rfl
      by_cases h:i≤B.origin f <;> simp [← hi,h]
    _≤_:=sum_le_sum fun i _=>sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast B.nested i j) (zqJ (jumpN i j))
theorem weakDual (B:aAU) (hline :Absorbs) (hc : ∀ o j,unit o j≤ iL o j)
    (hp : ∀ o s k,corePrice o s k≤a3D o s k) :
    (∑ f∈B.factors,(lineCharge f (B.line f) +
      ∑ s :bAL,FP (stopPrice a b z ar br (B.origin f) s) (B.stops f s))) ≤
      globalBook+freeBook+factorBook := by
  calc
    _ ≤ ∑ f∈B.factors,(lineCharge f (B.line f) +
        ∑ s :bAL,FP (fun k=>a3D (B.origin f) s k+globalRate k) (B.stops f s)) := by
      refine sum_le_sum fun f hf=>add_le_add le_rfl (sum_le_sum fun s _ => ?_)
      refine dYl (B.nonneg f hf s) fun k => ?_
      exact (aE8 (B.origin f) s k).trans
        (add_le_add (hp (B.origin f) s k) le_rfl)
    _=(∑ f∈B.factors,∑ s :bAL,FP globalRate (B.stops f s)) +
        (∑ f∈B.factors,∑ s :bAL,FP (freePart (B.origin f) s) (B.stops f s)) +
        (∑ f∈B.factors,(lineCharge f (B.line f) +
          ∑ s :bAL,FP (residual (B.origin f)) (B.stops f s))) := by
      simp only [FP,a3D,Pi.add_apply,add_mul,sum_add_distrib]
      abel
    _≤_:=add_le_add (add_le_add (global_bound B) (free_bound B)) (aNI B hline hc)
end
end qrT6Ada
end
section
set_option autoImplicit true
set_option exponentiation.threshold 160
namespace qrT6Ada
noncomputable section
open Finset q3rjQGe
open P6_7_1 (Origin introCap paidFee prefixFee bgK)
open TD (FP a3x)
open scoped BigOperators
theorem unit_le (o:Origin) (j:Fin 3) :unit o j≤ iL o j:= by
  have h (i:Origin) : (if i≤o then a4Q i j else 0) =
      ((if i≤o then jumpN i j else 0:ℕ) :ℚ) := by split <;> rfl
  simp only [unit,residual,iL,h,← z2R,← zCt,Nat.cast_le,
    zCS,zDT]
  fin_cases o <;> fin_cases j <;> decide
private def cP (i:Origin) :ℕ :=
  ([0x9a20fab49ae5bb,0x1230d4f828f5a82,0,0x137c9bbac4b5d8,0x268ee1048e3a1e,0x1a40dfde57ee4,
    0x603621d5dfcaa3,0x92c3092b0bc89,0,0,0x2c78330bea78a7,0,0] :List ℕ).get i
private theorem bdD:factorBook=((0x28eb85a68ddaeea :ℕ) :ℚ) := by
  have row (i:Origin) : (∑ j,a4Q i j*(introCap i.val j:ℚ))=(cP i:ℚ) := by
    simp only [a4Q,← z2R,← zCt,Nat.cast_inj,
      zCS,zDT]
    fin_cases i <;> decide
  simp only [factorBook,row,← zCt,Nat.cast_inj,zCS]
  decide
private def oldN (v :Origin→ℕ) (i:ℕ) :ℕ:=((List.ofFn v).take i).foldl max 0
private def billN (k :Fin 4) (j:Fin 3) :ℕ :=
  ∑ i:Origin,
    let v := fun o=>mixedCols (originShape o) k j
    (max (v i) (oldN v i.val) - oldN v i.val)*introCap i.val j
private theorem cast_fold (j:Fin 3) (L:List (Fin 3→ℕ)) (a :ℕ) :
    (↑(L.foldl (fun n w=>max n (w j)) a) :ℚ) =
      (L.map (fun w l=>(w l:ℚ))).foldl (fun n w=>max n (w j)) (a :ℚ) := by
  induction L generalizing a with
  | nil=>rfl
  | cons w L ih=>simp only [List.foldl_cons,List.map_cons,ih,Nat.cast_max]
private theorem old_cast (v :Origin→Fin 3→ℕ) (i:ℕ) (j:Fin 3) :
    (((List.ofFn (fun o l=>(v o l:ℚ))).take i).foldl (fun n w=>max n (w j)) 0) =
    (oldN (fun o=>v o j) i:ℚ) := by
  rw [List.ofFn_comp' v (fun w l=>(w l:ℚ)),← List.map_take,← Nat.cast_zero,← cast_fold]
  unfold oldN
  rw [List.ofFn_comp' v (fun w=>w j),← List.map_take,List.foldl_map]
private theorem bill_cast (k :Fin 4) :
    resourceBill (fun o j=>mixedCols (originShape o) k j) = ∑ j,(billN k j:ℚ) := by
  unfold resourceBill billN
  simp only [old_cast,zCt,z2R,Nat.cast_sub (le_max_right _ _),Nat.cast_max]
  exact sum_comm
private def billCols :Fin 4→Fin 3→ℕ :=
  ![![4785,3659,0],![0,77284,51788],![369996,0,235821],![0,0,4101845]]
private theorem bill_value (k :Fin 4) (j:Fin 3) :billN k j=billCols k j:= by
  simp only [billN,zCS]
  fin_cases k <;> fin_cases j <;> decide
def initialN :Fin 4→ℕ := ![8456,129214,609225,4122009]
theorem au9 (k :Fin 4) :initialBound k=(initialN k :ℚ) := by
  unfold initialBound
  rw [bill_cast]
  simp only [bill_value,← zCt,← Nat.cast_add,Nat.cast_inj,zCj]
  fin_cases k <;> decide
private theorem globalValue :globalBook=((0x139e864106:ℕ) :ℚ) := by
  simp only [globalBook,FP,au9,globalRate,SS,← Nat.cast_add,
    ← z2R,← zCt,Nat.cast_inj,zCS,zDT]
  decide
private def freeN :Fin 4→ℕ := ![24104,310786,1397676,7779828]
private theorem allFree_le (k :Fin 4) :allFreeCap 0 k≤(freeN k :ℚ)/25:= by
  have hl:allFreeCap 0 k≤freeBound 0 3 k := by
    change min _ (freeBound 0 3 k)*(1 :ℚ)≤_
    rw [mul_one]
    exact min_le_right _ _
  have hs :kK (bgK (stage 3).free) (refShape 0) k=(freeN k :ℚ) := by
    simp only [kK,← z2R,← zCt,Nat.cast_inj,zCj]
    fin_cases k <;> decide
  exact hl.trans_eq (by
    have hd: (stage 3).dI.succ=25:= by decide
    rw [freeBound,hs,← Nat.cast_succ,hd,Nat.cast_ofNat])
private theorem charge (n d c up:ℕ) (hd:0<d) (h:n*c≤up*(d*25)) :
    (n:ℚ)/d*((c:ℚ)/25)≤(up:ℚ) := by
  rw [div_mul_div_comm]
  apply (div_le_iff₀ (show (0:ℚ)<(d:ℚ)*25 by positivity)).2
  exact_mod_cast h
private theorem free_le :freeBook≤((0x3f15eee815167a :ℕ) :ℚ) := by
  refine (a3x freeDual_nonneg allFree_le).trans ?_
  simp only [FP,zCS,zDT]
  change (dualNum0:ℚ)/500*((24104 :ℕ)/(25:ℚ)) +
    ((dualNum1 :ℚ)/500*((310786:ℕ)/(25:ℚ)) +
      ((dualNum2 :ℚ)/200*((1397676:ℕ)/(25:ℚ))+(0*_+0)))≤_
  simp only [zero_mul,add_zero]
  refine (add_le_add (charge _ _ _ 0x2acb48e7793e2b (by decide) (by decide))
    (add_le_add (charge _ _ _ 0xc2f23dadb155a (by decide) (by decide))
      (charge _ _ _ 0x81b8225c0c2f5 (by decide) (by decide)))).trans ?_
  exact_mod_cast (show 0x2acb48e7793e2b+(0xc2f23dadb155a+0x81b8225c0c2f5) ≤
    (0x3f15eee815167a :ℕ) by decide)
theorem books_le :globalBook+freeBook+factorBook+bankFee+paidFee≤(prefixFee :ℚ) := by
  rw [globalValue,bdD]
  refine (add_le_add (add_le_add (add_le_add (add_le_add le_rfl free_le) le_rfl)
    le_rfl) le_rfl).trans ?_
  exact_mod_cast (show 0x139e864106+0x3f15eee815167a+0x28eb85a68ddaeea +
    bankFee+paidFee≤prefixFee by decide)
end
end qrT6Ada
end
