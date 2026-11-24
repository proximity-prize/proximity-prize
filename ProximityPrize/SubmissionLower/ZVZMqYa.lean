import ProximityPrize.SubmissionLower.ZIo6oRc
import ProximityPrize.SubmissionLower.ZeFfOZc
import ProximityPrize.SubmissionLower.Zqby9gc
import ProximityPrize.SubmissionLower.ZhieYVb
import ProximityPrize.SubmissionLower.ZZekYUb
import ProximityPrize.SubmissionLower.ZIEouCe
import ProximityPrize.SubmissionLower.ZFAtzgb
set_option Elab.async false
open _root_ renaming Finset.range → z4x, Ideal → znc, LinearIndependent → z14, LinearIndependent.of_comp → zCu, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.eval → zY9, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.le_add_right → z8K, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.pos_of_ne_zero → zOl, Nat.sub_le → z7J, Submodule → zpI, Submodule.inclusion → zwh, Submodule.span → zLD
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qCReOzb
noncomputable section
open Finset
open scoped Classical
open P6 (K p)
open P6_7_4 (wordLift)
open q6nKpZc (Input FixedPartPair FixedTariff)
open qzVScmb (Guards gX)
open private collect from ProximityPrize.SubmissionLower.ZQDgS7b
open P5_7_2 (A Ls stages)
open q7F2qKe (nV au1 bankFee allShapes chosen_mem)
open cu (Shape Jet qD rD j9)
open DP (ad0)
open Polynomial
open DP (d3r)
open gT (tK FW)
open pI (oU abM)
open qQ (VN aJr)
open TD (aBh)
open akZ (aSK strip)
structure BankBook {b u del M Γ F} (x : @Input b u del M Γ F) (G:Guards b) where
  fixed : ∀ s (hs :s∈stages b),FixedPartPair x s hs
  anchor_strip:aSK (fixed _ G.anchor_mem).free
  gH :Finset K
  bound:gH.card≤bankFee b
  content_paid : ∀ γ∈Γ,qD (M.label γ) anchor_strip.content=0→γ∈gH
  b3r : ∀ s (hs :s∈stages b),∀ γ∈Γ,
    (FW (fixed s hs).free.equation (F.scalar γ)=0 ∨
      FW (fixed s hs).moving.equation (F.scalar γ)=0)→γ∈gH
theorem aS3 {b u del M Γ F} (x : @Input b u del M Γ F) {s :Shape} {W:ℕ}
    (hW:W<s.m*A) {P:Jet} (hP:P∈x.banks s W) :
    ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0:= by
  intro γ hγ
  let B:=F.mark γ hγ
  have hdegree : (j9 (F.scalar γ)).natDegree≤131071+M.iF.toNat := by
    rw [j9,natDegree_map]
    exact P6_7.aic F hγ
  refine atp.dPr x.crt (wordLift M) x.units _ _ (x.residues γ hγ)
    hdegree B.bad.support B.bad.dw ?_ s W hW P hP
  intro i hit
  rw [j9,ad0,eval_map,eval₂_hom,B.scalar_hits i hit]
  rfl
theorem bank_book {b u del M Γ F} (x : @Input b u del M Γ F) (G:Guards b)
    (uq:FixedTariff F b) :Nonempty (BankBook x G) := by
  let caps s (hs :s∈stages b) :oU (x.donors.staged s hs).free.jet s.free :=
    d3r x.crt (wordLift M) (chosen_mem (x.donors.staged s hs).free)
  let fixed (s :Ls) (hs :s∈stages b) :FixedPartPair x s hs := by
    let R:=x.donors.staged s hs
    exact ⟨Classical.choice (bRI.proof _ _ R.free.nonzero (caps s hs)),
      Classical.choice (bRI.proof _ _ R.moving.nonzero
        (d3r x.crt (wordLift M) (chosen_mem R.moving)))⟩
  obtain ⟨a⟩:=strip (x.donors.staged _ G.anchor_mem).free.nonzero
    (caps _ G.anchor_mem) (fixed _ G.anchor_mem).free
  let content:=Γ.filter fun γ=>qD (M.label γ) a.content=0
  have hcontent:content.card≤(p+1)*(nV b 0).free.U:= by
    let C:VN :=⟨a.content,a.content_ne,∅⟩
    have h:=aJr (T:=content) (fun _ _ _ _ h=>sub_left_inj.mp h)
      C (a.content_le.trans_lt G.anchor_small) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
    change content.card≤(p+1)*a.content.totalDegree+(∅ : Finset _).card at h
    simpa only [card_empty,add_zero] using h.trans (Nat.add_le_add_right
      (zBI _ a.content_le) _)
  let zero (E :tK) :=Γ.filter fun γ=>FW E (F.scalar γ)=0
  have zero_bound {B J:ℕ} (hg:aBh B J) {E :tK} (he :abM E B J) :
      (zero E).card≤au1 b B J :=
    uq B J hg E he (zero E) (filter_subset _ _) (fun _ hγ=>(mem_filter.mp hγ).2)
  let rowFee (s :Shape) :=(p+1)*s.U+au1 b s.B s.J
  let PN (s :Ls) (hs :s∈stages b) :=
    (zero (fixed s hs).free.equation∪(if s=nV b 0 then content else ∅)) ∪
      zero (fixed s hs).moving.equation
  have hc (s) (hs :s∈stages b) : (PN s hs).card≤ rowFee s.free+rowFee s.moving:= by
    obtain ⟨hf,hm⟩:=G.staged_ode s hs
    have hcf : (if s=nV b 0 then content else ∅).card≤(p+1)*s.free.U:= by
      split
      · next he=>simpa only [he] using hcontent
      · simp
    exact gX ((gX (zero_bound hf (fixed s hs).free.equation_caps) hcf).trans_eq (Nat.add_comm ..))
      ((zero_bound hm (fixed s hs).moving.equation_caps).trans (Nat.le_add_left _ _))
  obtain ⟨T,hb,hmem⟩:=collect (stages b) (fun s=>rowFee s.free+rowFee s.moving) PN hc
  have hmap (l:List Ls) :
      (l.map (fun s=>rowFee s.free+rowFee s.moving)).sum =
        ((l.flatMap fun s=>[s.free,s.moving]).map rowFee).sum:= by
    induction l with
    | nil=>rfl
    | cons s l ih =>
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append,
        List.map_nil,List.sum_nil,Nat.add_zero,ih]
  refine ⟨⟨fixed,a,T,?_,?_,?_⟩⟩
  · refine hb.trans ?_
    rw [hmap]
    unfold bankFee allShapes
    simp only [List.map_append,List.sum_append]
    exact (z8K _ _).trans (z8K _ _)
  · intro γ hγ hc
    apply hmem _ G.anchor_mem
    have hγc:γ∈content:=mem_filter.mpr ⟨hγ,hc⟩
    exact mem_union_left _ (mem_union_right _ (by rw [ite_eq_left rfl]; exact hγc))
  · intro s hs γ hγ h
    apply hmem s hs
    rcases h with h | h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hγ,h⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hγ,h⟩)
end
end qCReOzb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qCReOzb
noncomputable section
open Finset
open scoped Classical BigOperators
open P6 (p jG)
open q6nKpZc (I0)
open qzVScmb (Guards last charge)
open P5_7_2 (A fO)
open q7F2qKe (origins isLast originCutter originBudget fibreShape kK BC)
open gT (Ambient gk)
open pI (oU dM pN mass a5I F7)
open YX (bQz bjf eHX evL)
open qQ (aJr bNe)

open akZ (yE bKa caQ cfi)
open cu (Jet)
open private a8m bYs ddo from ProximityPrize.SubmissionLower.CR
open private b6z from ProximityPrize.SubmissionLower.D7
theorem geometric_cover {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    {b:fO} (G:Guards b) (D:ℕ→Finset Jet) (cut:ℕ→Jet→Jet)
    (rescue :ℕ→Jet→Bool)
    (hi : ∀ o∈origins b,∀ f∈D o,Irreducible f)
    (hp : ∀ o∈origins b,∀ f∈D o,oU (cut o f) (fibreShape b o (rescue o f)) ∧ ¬ f∣cut o f)
    (hl : ∀ o∈origins b,∀ f∈D o,rescue o f=true→isLast b o)
    (ht : ∀ i∈origins b,∀ j,
      ∑ o∈(origins b).filter (i ≤ ·),∑ f∈D o,yE f j≤originBudget b i j) :
    Nonempty (Parents F b D cut rescue) := by
  let idx :=(origins b).sigma D
  have each (a :Σ _:ℕ,Jet) (ha :a∈idx) :
      ∃ S:Finset (znc Ambient),bQz a.2 (cut a.1 a.2) S ∧
        (∀ q∈S,q.height=2∧bjf q) ∧
        dM S (fun k=>kK (yE a.2) (fibreShape b a.1 (rescue a.1 a.2)) k) ∧
        ∀ γ∈Γ,Mark F a.2 γ→Mark F (cut a.1 a.2) γ → ∃ q∈S,I0 F q γ:= by
    obtain ⟨ho,hf⟩:=mem_sigma.mp ha
    have hh:=hp a.1 ho a.2 hf
    have hirr :=hi a.1 ho a.2 hf
    have hpair :=b6z hirr hh.2
    have hj:=G.fibre_J a.1 (Nat.le_of_lt_succ (mem_range.mp ho)) (rescue a.1 a.2)
    obtain ⟨S,hs,hc⟩:=aRY.proof _ _ hpair
    obtain ⟨hfinite,hfit⟩:=a8m _ _ hpair _ _ (caQ hirr.ne_zero) hj
      (bKa _) hh.1 S hs
    refine ⟨S,hs,?_,fun k=>(hfit k).trans_eq (cfi _ _ hj k),
      fun γ _=>hc (M.label γ) (F.scalar γ)⟩
    intro q hq
    obtain ⟨hprime,hdim,hrow,hcut⟩:=hs q hq
    exact ⟨bYs hpair hprime hdim hrow hcut,hfinite q hq⟩
  let S (a :Σ _:ℕ,Jet) :=if h:a∈idx then Classical.choose (each a h) else ∅
  have spec (a :Σ _:ℕ,Jet) (ha :a∈idx) :=Classical.choose_spec (each a ha)
  have hS (a :Σ _:ℕ,Jet) (ha :a∈idx) :S a=Classical.choose (each a ha) :=
    dite_eq_left ha
  let all:=idx.biUnion S
  have total (k :Fin 4) : (∑ a∈idx,mass (S a) k)≤BC b k := by
    refine le_trans (b := ∑ a∈idx,kK (yE a.2) (originCutter b a.1) k)
      (sum_le_sum ?_) ?_
    · intro a ha
      obtain ⟨ho,hf⟩:=mem_sigma.mp ha
      rw [hS a ha]
      refine ((spec a ha).2.2.1 k).trans ?_
      apply sum_le_sum
      intro j _
      apply ztf
      cases he :rescue a.1 a.2 with
      | false=>simp only [fibreShape,Bool.false_eq_true,ite_false,le_rfl]
      | true =>
        have hlast :a.1=last b:=hl a.1 ho a.2 hf he
        simp only [fibreShape,ite_true,hlast]
        exact G.rescue_weight k j
    · simpa only [idx,sum_sigma] using charge b D ht k
  have hmass (k :Fin 4) :mass all k≤BC b k :=
    (pI.bhF idx S _).trans (total k)
  have geom (q:znc Ambient) (hq:q∈all) :
      q.IsPrime∧ringKrullDim (gk q)=2∧q.height=2∧bjf q:= by
    obtain ⟨a,ha,hq⟩:=mem_biUnion.mp hq
    rw [hS a ha] at hq
    exact ⟨((spec a ha).1 q hq).1,((spec a ha).1 q hq).2.1,(spec a ha).2.1 q hq⟩
  have small (q:znc Ambient) (hq:q∈all) (k :Fin 4) :pN q k<p :=
    ((evL hq k).trans (hmass k)).trans_lt (G.bq6 k)
  let dominant (q:znc Ambient) :=Function.Injective ((Ideal.Quotient.mk q).comp F7)
  let marks (q:znc Ambient) :=Γ.filter (I0 F q)
  let paidAt (q:znc Ambient) :=if pN q 0=0 ∨ ¬ dominant q then marks q else ∅
  let gH :=all.biUnion paidAt
  have each_paid (q:znc Ambient) (hq:q∈all) :
      (paidAt q).card≤(p+1)*pN q 2+pN q 3+pN q 0:= by
    obtain ⟨hprime,hdim,_,hfinite⟩:=geom q hq
    by_cases hz :pN q 0=0
    · obtain ⟨C,hc,hp,hcov⟩:=ddo q hprime hdim hfinite hz
      have h:= aJr (T:=marks q) (fun _ _ _ _ h=>sub_left_inj.mp h) C
        (hc.trans_lt (small q hq 2)) (fun γ hγ=>hcov _ _ (mem_filter.mp hγ).2)
      unfold paidAt
      rw [ite_eq_left (Or.inl hz)]
      exact h.trans (Nat.le_add_right_of_le (z9f (zBI _ hc) hp))
    · by_cases hd:dominant q
      · simp [paidAt,hz,hd]
      · unfold paidAt
        rw [ite_eq_left (Or.inr hd)]
        refine ((card_le_one.mpr fun y hy z hz => ?_).trans (zOl hz)).trans (Nat.le_add_left _ _)
        obtain ⟨hy,hm⟩:=mem_filter.mp hy
        obtain ⟨hz,hn⟩:=mem_filter.mp hz
        exact F.distinct hy hz (bNe (eHX hprime hd hm hn))
  let owner (q:znc Ambient) :Σ _:ℕ,Jet :=
    if h:q∈all then Classical.choose (mem_biUnion.mp h) else ⟨0,0⟩
  have owns (q:znc Ambient) (h:q∈all) :owner q∈idx∧q∈S (owner q) := by
    simpa only [owner,dite_eq_left h] using Classical.choose_spec (mem_biUnion.mp h)
  let Bp (o:ℕ) (f :Jet) :=(S ⟨o,f⟩).filter fun q =>
    owner q=⟨o,f⟩∧0<pN q 0∧dominant q
  have sub (o:ℕ) (f :Jet) :Bp o f⊆S ⟨o,f⟩:=filter_subset _ _
  refine ⟨⟨Bp,gH,?_,?_,?_,?_,?_,?_⟩⟩
  · refine (card_biUnion_le.trans (sum_le_sum each_paid)).trans ?_
    simp only [sum_add_distrib,← mul_sum]
    exact z9f (z9f (zBI _ (hmass 2)) (hmass 3)) (hmass 0)
  · intro o ho f hf q hq
    obtain ⟨hq,_,hpos,hdom⟩:=mem_filter.mp hq
    have ha : (⟨o,f⟩:Σ _:ℕ,Jet)∈idx :=mem_sigma.mpr ⟨ho,hf⟩
    have hall:q∈all:=mem_biUnion.mpr ⟨_,ha,hq⟩
    obtain ⟨hprime,hd,hh,hfinite⟩:=geom q hall
    have hmem:=(spec _ ha).1 q (hS _ ha ▸ hq)
    exact ⟨⟨hprime,hd,hfinite.Kw,hfinite.jU,hfinite.kK,hfinite.Bo,
      ⟨hpos,small q hall 0⟩,small q hall 2,small q hall 3,hdom⟩,hh,hmem.2.2⟩
  · intro o _ f _ i _ g _ q hq hr
    have he :=(mem_filter.mp hq).2.1.symm.trans (mem_filter.mp hr).2.1
    exact ⟨congrArg Sigma.fst he,congrArg (fun a :Σ _:ℕ,Jet=>a.2) he⟩
  · intro o ho f hf k
    have ha : (⟨o,f⟩:Σ _:ℕ,Jet)∈idx :=mem_sigma.mpr ⟨ho,hf⟩
    exact (a5I (sub o f) k).trans (by rw [hS _ ha]; exact (spec _ ha).2.2.1 k)
  · intro k
    refine (sum_le_sum fun o _=>sum_le_sum fun f _=>a5I (sub o f) k).trans ?_
    simpa only [idx,sum_sigma] using total k
  · intro o ho f hf γ hγ hz hw
    have ha : (⟨o,f⟩:Σ _:ℕ,Jet)∈idx :=mem_sigma.mpr ⟨ho,hf⟩
    obtain ⟨q,hq,hm⟩:=(spec _ ha).2.2.2 γ hγ hz hw
    have hall:q∈all:=mem_biUnion.mpr ⟨_,ha,(hS _ ha).symm ▸ hq⟩
    by_cases he :pN q 0=0 ∨ ¬ dominant q
    · exact Or.inl (mem_biUnion.mpr ⟨q,hall,by unfold paidAt; rw [ite_eq_left he]; exact mem_filter.mpr ⟨hγ,hm⟩⟩)
    · have hh:=owns q hall
      generalize howner :owner q=a at hh
      obtain ⟨i,g⟩:=a
      obtain ⟨hi,hg⟩:=mem_sigma.mp hh.1
      exact Or.inr ⟨i,hi,g,hg,q,mem_filter.mpr ⟨hh.2,howner,
        zOl (fun h=>he (Or.inl h)),not_not.mp fun h=>he (Or.inr h)⟩,hm⟩
end
end qCReOzb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qCReOzb
noncomputable section
open P6 (K jG)
open P5_7_2 (A Window)
open q7F2qKe (wX lineFee)
open qzVScmb (LineRow LineCaps)
open qckEfrc (Var Regular point)
open cu (Jet L FX kr)
open akZ (yE caQ)
open Finset MvPolynomial
open scoped Polynomial Classical
open private bLI from ProximityPrize.SubmissionLower.ZdSQxye
open private bd0 from ProximityPrize.SubmissionLower.ZqKag5d
open private e rename_caps bw from ProximityPrize.SubmissionLower.ZvttkHa
open qp56ikd (charged)
private theorem rename_root {u del} {M:jG u del} {Γ}
    {F:P1.bje A M Γ} {g:LineRow} {γ:K} (h:LineRoot F g γ) :
    ∃ z :L,Regular (rename e g) z (F.scalar γ) := by
  obtain ⟨z,hz⟩:=h
  have hp:point z (F.scalar γ) ∘ e =
      ![algebraMap L FX z,kr (F.scalar γ),kr (F.scalar γ).derivative] := by
    funext i
    fin_cases i <;> rfl
  refine ⟨z,?_⟩
  unfold Regular
  rw [show (some 1 :Var)=e 2 by rfl,pderiv_rename e.injective,
    eval_rename,eval_rename,hp]
  exact hz
theorem line_count {b u del} {M:jG u del} {Γ} {F:P1.bje A M Γ}
    (hband:Window b M.iF) {f :Jet} {g:LineRow}
    (hj:0<yE f 1) (hu:0<yE f 2) (hcaps :LineCaps f g) :
    (Γ.filter (LineRoot F g)).card≤lineFee b (yE f) := by
  classical
  have hf :f≠0:=Polynomial.ne_zero_of_natDegree_gt hj
  have hb:0<yE f 0:=hj.trans_le (caQ hf)
  have hd:2≤wX b :=
    (by decide :2≤131071).trans (z8K _ _)
  have hD:wX b≤133774 :=z3b (bLI b).2 131071
  let T:=Γ.filter (LineRoot F g)
  let G:=rename e g
  have hz (γ:K) : ∃ z :L,γ∈T→Regular G z (F.scalar γ) := by
    by_cases hγ:γ∈T
    · obtain ⟨z,hz⟩:=rename_root (mem_filter.mp hγ).2
      exact ⟨z,fun _=>hz⟩
    · exact ⟨0,fun h=>(hγ h).elim⟩
  choose z hz using hz
  have hw:=bd0 F hband (show T⊆Γ from filter_subset _ _)
  have hc:=charged hw hd hD hb hj hu (rename_caps hcaps) z hz
  exact bw (hD.trans_lt (by decide)) hc
end
end qCReOzb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q7cZjxe
noncomputable section
open Polynomial
open P6 (K jG)
open P5_7_2 (A row stages anM)
open q7F2qKe (nV)
open q6nKpZc (Input)
open qCReOzb (anchor Mark LineRoot)
open qCQTZAc (LiftAt degreeBound liftHeight declared_le)
open cu (FX Jet kr)
open DP (U4 Aw awN)
open private bLI from ProximityPrize.SubmissionLower.ZdSQxye
open private shape_bound from ProximityPrize.SubmissionLower.ZaOaNGc
open private flat rawFlat center_flat lift_factor flat_scalar bounded_iff expand weight from ProximityPrize.SubmissionLower.Zl6SIrc
private theorem overhead_le {b u del M Γ F} (x : @Input b u del M Γ F) :
    M.iF≤2703:=x.vo.2.trans (by exact_mod_cast ((bLI b).1.trans (declared_le b)))
theorem scalar_le {b u del M Γ F} (x : @Input b u del M Γ F) {γ:K} (hγ:γ∈Γ) :
    (F.scalar γ).natDegree≤degreeBound:= by
  have hw:=overhead_le x
  have hn:M.iF.toNat≤2703:= by omega
  exact (P6_7.aic F hγ).trans (z3b hn _)
theorem lift_of_anchor {b u del M Γ F} (x : @Input b u del M Γ F)
    (h:nV b 0∈stages b) {f :Jet} (hf :Irreducible f) (hd:f∣anchor x h) :
    LiftAt degreeBound liftHeight f := by
  let s :=nV b 0
  let R:=(x.donors.staged s h).free
  have hmap :=map_dvd (flat FX).toRingHom hd
  change flat FX f∣flat FX (U4 R.raw) at hmap
  rw [center_flat] at hmap
  have hraw:rawFlat R.raw≠0:= by
    intro hz
    have he :=center_flat R.raw
    rw [hz,map_zero] at he
    exact R.nonzero ((flat FX).toRingEquiv.map_eq_zero_iff.mp he)
  have hfi:Irreducible (flat FX f) :=hf.map (flat FX).toRingEquiv
  obtain ⟨q,hq,v,hv,he⟩:=lift_factor hfi (rawFlat R.raw) hraw hmap
  let P:=rawFlat.symm q
  have hP:rawFlat P=q:=rawFlat.apply_symm_apply q
  refine ⟨P,v,hv,(flat FX).injective ?_,?_⟩
  · rw [center_flat,hP,he,map_mul,flat_scalar]
  · have hamb:R.raw∈Aw M.iF.toNat s.free (anM M.iF.toNat s.dI s.free) :=
      R.mem.1.1
    have hbound: (expand (rawFlat R.raw)).weightedTotalDegree (weight degreeBound (degreeBound-1))≤liftHeight :=
      (bounded_iff _ _ _ _).mpr fun j i a e hc=> by
        have hel:awN M.iF.toNat s.free (anM M.iF.toNat s.dI s.free) j i a e :=
          by_contra fun hn=>hc (hamb j i a e hn)
        obtain ⟨hm,hB,hJ⟩:=shape_bound b
        have hX:M.iF.toNat≤2703:= by have hh:=overhead_le x; omega
        have hcut:anM M.iF.toNat s.dI s.free≤100*A :=
          (z7J ..).trans ((z7J ..).trans (ztf A hm))
        have hclear : (s.free.B+s.free.J)*(2*M.iF.toNat)≤(150+150)*(2*2703) :=
          Nat.mul_le_mul (z9f hB hJ) (zBI 2 hX)
        have hx :=hel.2.2.2
        have hj:=hel.2.1.trans hJ
        have hjet:=zBI degreeBound (hel.1.trans hB)
        rw [Nat.mul_add] at hjet
        have hvel:=ztf j (z7J degreeBound 1)
        change a+133774*i+133773*j≤0x5f5e100
        change 133774*i+133774*j≤133774*150 at hjet
        change 133773*j≤133774*j at hvel
        change _≤100*179740 at hcut
        omega
    apply (bounded_iff _ _ _ _).mp
    rw [hP]
    exact (MvPolynomial.weightedTotalDegree_le_of_dvd _ (map_dvd expand.toRingHom hq)
      ((map_ne_zero_iff _ expand.injective).mpr hraw)).trans hbound
open Finset
open qzVScmb (LineRow LineCaps)
open qaySLPd (RS ConstantFibre)
open q89hPdc (linePoint regular_line)
open private curve witness JX base witness_eval nonzero_projection restrict restrict_caps restrict_eval restrict_derivative from ProximityPrize.SubmissionLower.Z0SAUab
theorem line_of_fibres {u del} {M:jG u del} {Γ}
    (F:P1.bje A M Γ) (f :Jet) (T:Finset K)
    (hT : ∀ γ∈T,¬ Mark F f.derivative γ∧ConstantFibre f (M.label γ) (F.scalar γ)) :
    ∃ row:LineRow,LineCaps f row ∧ ∀ γ∈T,LineRoot F row γ:= by
  classical
  let S (i:T) :=F.scalar i
  let z (i:T) :=M.label i
  choose q hq hqz hqd using fun i:T=>curve f (z i) (S i) (hT i i.property).2
  have hsep (i:T) :JX (witness (z i)) (RS f.derivative (S i))≠0:= by
    rw [witness_eval]
    exact (hT i i.property).1
  choose g hg hg' using fun i:T=>nonzero_projection _ _ (hsep i)
  obtain ⟨s,b,hline⟩:=regular_line q g (witness ∘ z) hq hqz hg
  refine ⟨restrict s b f,restrict_caps s b f,?_⟩
  intro γ hγ
  let i:T:=⟨γ,hγ⟩
  obtain ⟨a,ha,hb⟩:=hline i
  refine ⟨a,?_,?_⟩
  · change zY9 ![base a,kr (S i),kr (S i).derivative] (restrict s b f)=0
    rw [restrict_eval]
    have hd:=map_dvd (JX (linePoint s b a)) (hqd i)
    have hz :JX (linePoint s b a) (MvPolynomial.map base (q i))=0:= by
      rw [JX,← MvPolynomial.map_eval,ha,map_zero]
    rwa [hz,zero_dvd_iff] at hd
  · change zY9 ![base a,kr (S i),kr (S i).derivative]
      (MvPolynomial.pderiv 2 (restrict s b f))≠0
    rw [restrict_derivative,restrict_eval]
    exact hg' i _ hb
end
end q7cZjxe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qqW9Gbd
noncomputable section
open K1 (I)
open cu (L FX Shape Jet)
open DP Polynomial
open scoped BigOperators
open private Position azk bwM dPW anL aMr gs6 en2 cqC from ProximityPrize.SubmissionLower.Z
open private gNq from ProximityPrize.SubmissionLower.ZeFfOZc
section
variable {h:ℕ} {D:jF h} (Crt:zG D) (word:I→L) (s :Shape)
  (S:zpI L Source)
private abbrev S6 (W:ℕ) :=complete Crt word s W ⊓ S
private instance layerFinite (W:ℕ) :zAa L (S6 Crt word s S W) :=
  Module.Finite.of_injective (zwh inf_le_left)
    (Submodule.inclusion_injective (inf_le_left:S6 Crt word s S W≤ complete Crt word s W))
private abbrev aV (W:ℕ) :zpI FX Jet :=
  zLD FX (U4 '' (S6 Crt word s S W:Set Source))
private def boundary (W:ℕ) :S6 Crt word s S W →ₗ[L] (Position→L) :=
  (aMr Crt word s W).comp (zwh inf_le_left)
private theorem layer_boundary_rank (W:ℕ) :
    zsE L (boundary Crt word s S W).range≤zsE FX (aV Crt word s S W) := by
  classical
  let F:=boundary Crt word s S W
  let b:=Module.finBasis L F.range
  have hex (k :Fin (zsE L F.range)) :
      ∃ P:S6 Crt word s S W,F P=(b k :Position→L) :=(b k).property
  choose P hP using hex
  have hli:z14 L (fun k t =>
      (bwM (P k :Source) t).coeff (anL h s W t)) := by
    change z14 L (F ∘ P)
    rw [show F ∘ P=fun k=>((b k :F.range) :Position→L) from funext hP]
    exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
  have heval :z14 FX (fun k=>U4 (P k :Source)) := by
    apply zCu azk
    have hf :azk ∘ (fun k=>U4 (P k :Source)) =
        fun k t=>algebraMap L[X] FX (bwM (P k :Source) t) :=
      funext fun k=>funext fun t=>dPW (P k :Source) t
    rw [hf]
    exact en2 (fun k=>bwM (P k :Source)) (anL h s W)
      (fun k=>gs6 (⟨P k,(P k).property.1⟩:complete Crt word s W)) hli
  let u (k :Fin (zsE L F.range)) :aV Crt word s S W :=
    ⟨U4 (P k :Source),Submodule.subset_span ⟨_,(P k).property,rfl⟩⟩
  have hu:z14 FX u :=
    zCu (aV Crt word s S W).subtype heval
  have :zAa FX (aV Crt word s S W) := by
    change zAa FX
      (zLD FX ((S6 Crt word s S W).map U4.toLinearMap:Set Jet))
    exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A:=FX))
  simpa [F] using hu.fintype_card_le_finrank
private theorem layer_strict {W:ℕ} (P: (boundary Crt word s S W).ker)
    {j i a e} (hn:Fg (P.1 :Source) j i a e≠0) :
    a+(i+j)*(131071+h)<W+(s.B+s.J)*(2*h)+j:= by
  let z :complete Crt word s W:=⟨P.1,P.1.property.1⟩
  exact cqC (⟨z,P.property⟩: (aMr Crt word s W).ker) hn
private theorem layer_ker_step (W:ℕ) :
    zsE L (boundary Crt word s S (W+1)).ker ≤
      zsE L (S6 Crt word s S W) := by
  let F:=boundary Crt word s S (W+1)
  have hm (P:F.ker) : (P.1 :Source)∈S6 Crt word s S W:= by
    refine ⟨⟨⟨?_,P.1.property.1.1.2⟩,P.1.property.1.2⟩,P.1.property.2⟩
    intro j i a e hb
    by_contra hn
    have he :awN h s (W+1) j i a e := by
      by_contra hh
      exact hn (P.1.property.1.1.1 j i a e hh)
    have hl:=layer_strict Crt word s S P hn
    exact hb ⟨he.1,he.2.1,he.2.2.1,by omega⟩
  let f :=((S6 Crt word s S (W+1)).subtype.comp F.ker.subtype).codRestrict
    (S6 Crt word s S W) hm
  apply LinearMap.finrank_le_finrank_of_injective (f :=f)
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x :S6 Crt word s S W=>(x :Source)) he
theorem telescope (hhi:h≤131070) (W:ℕ) :
    zsE L (complete Crt word s W ⊓ S:zpI L Source) ≤
      ∑ t∈z4x (W+1),zsE FX
        (zLD FX (U4 '' ((complete Crt word s t ⊓ S:zpI L Source) :Set Source))) := by
  change zsE L (S6 Crt word s S W) ≤
    ∑ t∈z4x (W+1),zsE FX (aV Crt word s S t)
  induction W with
  | zero =>
    have hk : (boundary Crt word s S 0).ker = ⊥ := by
      apply bot_unique
      intro P hP
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply gNq hhi Crt s P P.property.1.2
      intro j i a e hn
      simpa only [zero_add] using layer_strict Crt word s S ⟨P,hP⟩ hn
    have hr :=(boundary Crt word s S 0).finrank_range_add_finrank_ker
    rw [hk,finrank_bot,add_zero] at hr
    simpa [← hr] using layer_boundary_rank Crt word s S 0
  | succ W ih =>
    rw [Finset.sum_range_succ]
    have hr :=(boundary Crt word s S (W+1)).finrank_range_add_finrank_ker
    have ha :=layer_boundary_rank Crt word s S (W+1)
    have hb:=layer_ker_step Crt word s S W
    omega
end
end
end qqW9Gbd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qqW9Gbd
noncomputable section
open K1 (I)
open cu (L FX)
open DP (jF zG Source complete c69)
open P6_7_1
open scoped BigOperators
def c1 :Prop :=
  ∀ (h:ℕ) (word:I→L) (s :Rectangle) (W:ℕ),
    zsE L (rectAmbient h s W) ≤
      contactDebit s+Module.finrank L (rectContacted h word s W)
def c2 :Prop :=
  ∀ (h:ℕ) (D:jF h) (Crt:zG D) (word:I→L) (s :Rectangle) (W:ℕ),
    0<h→h<K1.p→s.J≤ s.B→s.B<K1.p→s.B≤ s.z→s.B≤ s.t →
    zsE L (rectContacted h word s W)≤ iL h s+h*aWs s*(s.z+s.t+2) +
      zsE L (complete Crt word s.box W ⊓ seedBox s.z s.t:zpI L Source)
private theorem subWidth_ge (i:jJ) :2093≤ subWidth i:= by
  have h : ∀ k∈gw,2093≤(k :ℕ×ℕ).2 := by
    rw [gw]
    repeat' refine List.forall_mem_cons.mpr ⟨by decide,?_⟩
    simp
  exact le_min (by decide) (h _ (List.get_mem ..))
private theorem tested_widths (t:Test) : (Lc t).B≤(Lc t).z∧(Lc t).B≤(Lc t).t:= by
  rcases t with _ | ⟨i,a⟩
  · exact ⟨by decide,by decide⟩
  · by_cases h:a=0
    · rw [Lc,ite_eq_left h]
      exact ⟨subWidth_ge i,(by decide :terminal.B≤terminal.t)⟩
    · rw [Lc,ite_eq_right h]
      exact ⟨(by decide :terminal.B≤terminal.z),subWidth_ge i⟩
private theorem cutoff_succ (s :Rectangle) (hm:s.m=terminal.m) :
    rectCut s+1=terminal.m*P6.dw:= by
  change s.m*P6.dw-1+1= _
  rw [hm,Nat.sub_add_cancel (by decide)]
private theorem terminal_floor (h₁:c1) (h₂:c2) {x :Input} (P:Poles x) (t:Test) :
    rectVolume x.h (Lc t)≤ rectDebit x.h (Lc t) +
      ∑ W∈z4x (terminal.m*P6.dw),zsE FX (rectBank P (Lc t) W) := by
  let s :=Lc t
  let W:=rectCut s
  obtain ⟨hm,hB,hJ,_,_⟩:s.m=terminal.m∧s.B=terminal.B∧s.J=terminal.J∧_:=ctc t
  have ⟨hz,ht⟩:s.B≤ s.z∧s.B≤ s.t:=tested_widths t
  obtain ⟨hlo,hhi⟩:=heights x
  have hh:x.h≤131070:=hhi.trans (by decide)
  have hw:c69 x.h s.box W:= by
    intro q hq j _
    have hb:q≤terminal.B:=hq.trans_eq hB
    have hwidth :terminal.B*(131071-packetLo)≤terminal.m*P6.dw:= by decide
    rw [cutoff_succ s hm]
    exact ((Nat.mul_le_mul hb (Nat.sub_le_sub_left hlo _)).trans hwidth).trans (z8K _ _)
  have hvol:=bT9 (hh.trans (by decide)) s W hw
  have hphys :=h₁ x.h x.word s W
  have hpole :=h₂ x.h P.D P.crt x.word s W (lt_of_lt_of_le (by decide) hlo)
    (hh.trans_lt (by decide)) (hJ.trans_le ((by decide :terminal.J≤terminal.B).trans_eq hB.symm))
    (hB.trans_lt (by decide)) hz ht
  have hsum:=telescope P.crt x.word s.box (seedBox s.z s.t) hh W
  change zsE L (rectComplete P s W) ≤
    ∑ w∈z4x (rectCut s+1),zsE FX (rectBank P s w) at hsum
  rw [cutoff_succ s hm] at hsum
  change zsE L (rectContacted x.h x.word s W) ≤
    iL x.h s + x.h*aWs s*(s.z+s.t+2)+Module.finrank L (rectComplete P s W) at hpole
  have hcut:W+1=s.m*P6.dw:=(cutoff_succ s hm).trans (congrArg (· * P6.dw) hm.symm)
  rw [hcut] at hvol
  change rectVolume x.h s+iL x.h s≤_ at hvol
  change rectVolume x.h s≤(contactDebit s + x.h*aWs s*(s.z+s.t+2)) +
    ∑ w∈z4x (terminal.m*P6.dw),zsE FX (rectBank P s w)
  omega
theorem of_children (h₁:c1) (h₂:c2) :P6_7_1.c4 := by
  intro x P
  exact ⟨terminal_floor h₁ h₂ P,fun t=>rectShift P (Lc t)⟩
end
end qqW9Gbd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
open P6_7_1
private def checkedB (i:ℕ) (ps:List (ℕ×ℕ)) :Bool:=
 List.rec (motive:=fun _=>ℕ→Bool) (fun _=>true) (fun p _ r i=>check i (min terminal.z p.2) (min terminal.z p.1+1) && r (i+1)) ps i
private theorem checked_of {i:ℕ} {ps:List (ℕ×ℕ)} (h:checkedB i ps=true) :checked i ps := by
 induction ps generalizing i with
 | nil=>exact True.intro
 | cons p ps ih=>
   have h':(check i (min terminal.z p.2) (min terminal.z p.1+1) && checkedB (i+1) ps)=true:=h
   rw [Bool.and_eq_true] at h'
   exact ⟨h'.1,ih h'.2⟩
end qUlPTla
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem Wp:checked 1 (segment 0) :=checked_of (by decide +kernel)
set_option maxRecDepth 4096 in
theorem ordinary_check :check 101 60836 0=true :=rfl
end qUlPTla
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem Z3:checked 26 (segment 25) :=checked_of (by decide +kernel)
end qUlPTla
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem aib:checked 51 (segment 50) :=checked_of (by decide +kernel)
end qUlPTla
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem akh:checked 76 (segment 75) :=checked_of (by decide +kernel)
end qUlPTla
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_2_3Q133
open aR (Shape)
open qmb8rCe (sumN fullCost factor)
open qOPkAYa (Filed base countedRank fastMass flags fastPart checked part_tail)
theorem fil {a :Shape} {d n r f p:ℕ} (hn:sumN (base a) (a.b+1)=n)
    (hr :sumN (countedRank a) (a.b+1)=r) (hf :sumN (fullCost a (a.b-1)) (a.b+1)=f)
    (hp:sumN (fastPart a (a.b-1)) (a.b+1)=p) (h:r≤n∧f+p≤a.b*n+d) :Filed a d:= by
  unfold Filed; dsimp only; rw [hn,hr,hf,hp]; exact h
theorem congr {f g:ℕ→ℕ} : ∀ {n},(∀ i<n,f i=g i)→sumN f n=sumN g n
  | 0,_=>rfl
  | n+1,h=> by
    show sumN f n+f n=sumN g n+g n
    rw [congr fun i hi=>h i (by omega),h n (by omega)]
theorem tl {a :Shape} {U k l n y :ℕ} (hk :fastMass a a.j 0=k) (hl:flags a a.j=l)
    (h:sumN (fun i=>factor a U (a.j+i)*k+l) n=y) :
    sumN (fun i=>fastPart a U (a.j+i)) n=y :=
  (congr fun _ _=>part_tail (by omega) hk hl).trans h
set_option quotPrecheck false in
local notation "k!" hh:arg nn:arg kk:arg yy:arg=>checked (n:=nn) (k :=kk) (y :=yy) hh (by decide +kernel)
private abbrev a1 :Shape :=⟨87,27,12⟩
private theorem r1_0:sumN (countedRank a1) 88=991536:=k! rfl 0 88 991536
private theorem f1_0:sumN (fullCost a1 86) 88=0x53b1dc2 :=k! rfl 0 88 0x53b1dc2
private theorem p1_0:sumN (fastPart a1 86) 27=5072964 :=k! rfl 0 27 5072964
theorem proof1 :qOPkAYa.c1 :=
  fil (a :=a1) (n:=991536) (r :=991536) (f :=0x53b1dc2) (p:=0xd7dba6) (by decide +kernel) r1_0 f1_0
    (checked (k :=61) (y :=9073506) p1_0 (tl (k :=1924) (l:=33306) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
    (by decide)
private abbrev a2 :Shape :=⟨164,50,19⟩
private theorem r2_0:sumN (countedRank a2) 95=6959520:=k! rfl 0 95 6959520
private theorem ao0:sumN (countedRank a2) 165=0xa3f520:=k! r2_0 95 70 3785600
private theorem f2_0:sumN (fullCost a2 163) 95=0x575d69c8:=k! rfl 0 95 0x575d69c8
private theorem f2_1 :sumN (fullCost a2 163) 165=0x6aa8d3a0:=k! f2_0 95 70 0x134b69d8
private theorem p2_0:sumN (fastPart a2 163) 37=0x3c08332 :=k! rfl 0 37 0x3c08332
private theorem p2_1 :sumN (fastPart a2 163) 50=0x6197f8e :=k! p2_0 37 13 0x258fc5c
theorem proof2 :qOPkAYa.c2 :=
  fil (a :=a2) (n:=0xa3f520) (r :=0xa3f520) (f :=0x6aa8d3a0) (p:=0x11569620) (by decide +kernel) ao0 f2_1
    (checked (k :=115) (y :=0xb3d1692) p2_1 (tl (k :=11250) (l:=357090) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
    (by decide)
private abbrev a3:Shape :=⟨174,52,22⟩
private theorem r3_0:sumN (countedRank a3) 101=8760631 :=k! rfl 0 101 8760631
private theorem a7h:sumN (countedRank a3) 175=0xcced34 :=k! r3_0 101 74 4669437
private theorem f3_0:sumN (fullCost a3 173) 101=0x7546d4c6:=k! rfl 0 101 0x7546d4c6
private theorem f3_1 :sumN (fullCost a3 173) 175=0x8e893de0:=k! f3_0 101 74 0x1942691a
private theorem p3_0:sumN (fastPart a3 173) 39=0x4cade02 :=k! rfl 0 39 0x4cade02
private theorem p3_1 :sumN (fastPart a3 173) 52=0x79e7c40:=k! p3_0 39 13 0x2d39e3e
theorem proof3:qOPkAYa.c3 :=
  fil (a :=a3) (n:=0xcced34) (r :=0xcced34) (f :=0x8e893de0) (p:=0x16116398) (by decide +kernel) a7h f3_1
    (checked (k :=123) (y :=0xe72e758) p3_1 (tl (k :=12719) (l:=419106) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
    (by decide)
end P5_7_2_3Q133
end
section
set_option autoImplicit true
namespace qcCIx1d
theorem proof :qAFIJ5c.c2 :=
  qje58fc.of_children qnRjM0a.proof qVljrgb.proof
    (qOPkAYa.of_children P5_7_2_3Q133.proof1 P5_7_2_3Q133.proof2
      P5_7_2_3Q133.proof3)
end qcCIx1d
end
section
set_option autoImplicit true
namespace q8pCIub
theorem proof :qAFIJ5c.c3 :=
  qAzyIze.of_children qOhg0Kc.proof qal8fRb.proof
end q8pCIub
end
section
set_option autoImplicit true
namespace qDDNOOe
open P5_7_2 (fO)
open q7F2qKe (origins stops afterFree)
open q5oHm3d (dqs)
def c1 :Prop := ∀ (b:fO),b.val = 2 → ∀ o∈origins b,∀ j∈stops b,
  afterFree b<j→dqs b o j
def c2 :Prop := ∀ (b:fO),b.val=3 → ∀ o∈origins b,∀ j∈stops b,
  afterFree b<j→dqs b o j
def c3:Prop := ∀ (b:fO),b.val = 4 → ∀ o∈origins b,∀ j∈stops b,
  afterFree b<j→dqs b o j
def c4 :Prop := ∀ (b:fO),b.val=5 → ∀ o∈origins b,∀ j∈stops b,
  afterFree b<j→dqs b o j
def c5:Prop := ∀ (b:fO),b.val=6 → ∀ o∈origins b,∀ j∈stops b,
  afterFree b<j→dqs b o j
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :
    qJkiHnb.c1 := by
  intro b hb2 hb7 o ho j hj hl
  have :b.val = 2∨b.val=3∨b.val = 4∨b.val=5∨b.val=6:= by omega
  rcases this with h | h | h | h | h
  · exact h1 b h o ho j hj hl
  · exact h2 b h o ho j hj hl
  · exact h3 b h o ho j hj hl
  · exact h4 b h o ho j hj hl
  · exact h5 b h o ho j hj hl
end qDDNOOe
end
section
set_option autoImplicit true
namespace qaxPAkd
theorem proof :qJkiHnb.c2 :=qXrbKzb.proof
end qaxPAkd
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace P5_7_2_3Q723
open P5_7_2 (fO)
open q7F2qKe (originCount stopCount origins stops afterFree)
open q5oHm3d (dqs)
open qr4gGVa
open private NK Jj from ProximityPrize.SubmissionLower.ZjjMFxd
set_option quotPrecheck false in
local notation "arith!" => of_decide_eq_true (by with_unfolding_all rfl)
set_option quotPrecheck false in
local notation "receipt!" ww:arg x:arg =>
  row_of_checks x ww
    (by first | exact projection_box arith! | exact projection_stage (i:=7) arith! arith! arith!)
    arith! arith! (by with_unfolding_all rfl) (by intro k; fin_cases k <;> exact arith!)
private theorem r12_9 (o:Fin 13) :dqs b12 o 9:= by
  fin_cases o <;> exact receipt! NK 0xe0000100000addd4f6380000400002cb9e8d4e0001900011300126240000640003e75447d120000500002c5274c8580000400001f34a02920000500002c0981fa60000640002a07399618001a9000b8993a5627000064000246be8aee2001a9000811274cae800006400020f612fc2c000550001433e673c
private theorem r12_10 (o:Fin 13) :dqs b12 o 10 := by
  fin_cases o <;> exact receipt! NK 0xc0003100029ec0e1ba34000038b3faf743eb4c0003100026dccfaae3000004000032fd3c88e00005000038be84ec4000004000027c3a7c0e000550003beb7de0048000040000226e90e5200001000008d83992580000400001d8cc9e5a001a9000a4dda70f160006a4002cc40072d220005500019d23cf24
private theorem r12_11 (o:Fin 13) :dqs b12 o 11 := by
  fin_cases o <;> exact receipt! NK 0xc0000100000df8593f3200001d2d346fb3d5cc000790006010a09f33000004000036fa0d40e000790005d428c42130001e400182609e294e0080900626094c85b38001e400158e4018b4e001a900139d8fffb84000004000027487c8d4001a9000dd3c22a1848006a4003c1feaa331a0005500022ad0afa6
private theorem r12_12 (o:Fin 13) :dqs b12 o 12 := by
  fin_cases o <;> exact receipt! NK 0xa000010000101b436f2800484004c55cfa1e4c0000100000e7833e7280000400003f4220ecc0000100000dfd950f300000400003a3d7ffcc0000100000de04da4300000400003327a37cc0000100000e35a37730006a40056bf2b5d10e0000100000b2439ef38006a4005078c032c1200001000008bc4749
private theorem r12_13 (o:Fin 13) :dqs b12 o 13:= by
  fin_cases o <;> exact receipt! NK 0xa0027100271b28f9f628001f4002101484eacc0000100000df4cdd6280001400013a713070c0000100000d551b8a30000040000385413a8c0000100000d2e676d380000400002f073e28d00000d9e233a4e4e530006a400594a49075500000100000ac8b73e380000400002be83291000001000009ca06bd
private theorem r13_9 (o:Fin 13) :dqs b13 o 9:= by
  fin_cases o <;> exact receipt! Jj 0x100000100000ac6e062380000400002c50ea0ce0000100000ae5670140000040000279da431200001000008c882904800004000022e35c49400001000007e15cc260000440001d445e0398000110000713dbd7870000140000736f4e06000011000058d0819488000440001475d231ac000110000400a7bb0
private theorem r13_10 (o:Fin 13) :dqs b13 o 10 := by
  fin_cases o <;> exact receipt! Jj 0xd00000d915347b6db7300001c0001890d7738c00007000057f577643000004000032808340e0000100000b3cc9cf38000440002f70cabb900000100000a0725ca4800004000023094981400001000008857cd1580000400001d40aafd800001000006ac7da768001540008296ce246200011000051ccb557
private theorem r13_11 (o:Fin 13) :dqs b13 o 11 := by
  fin_cases o <;> exact receipt! Jj 0xc0000100000dda425c30001e4001b51677d8cc000790005f257bab5300000400003673ef48e000790005c5569a26380202401855ca5f684c0080900676f7f38dc38006a4004da3da3bace00809005a9d1c98964000004000026dc292d3000008f4aafd13e0b50006a40036b6f23511a0000500002047e97f
private theorem r13_12 (o:Fin 13) :dqs b13 o 12 := by
  fin_cases o <;> exact receipt! Jj 0xa0012100120932c686288000085f96c0dacbcc0000100000e559e1a28004840046bf4603f8c0000100000ddaa8363000004000036ecdb98a0012100109b7c2a6a3000484003f7c3e0978c0000100000ca66c2b30006a40055c5c7b050e001a90013e36b7188380000400002c102091200001000008a2b56f
private theorem r13_13 (o:Fin 13) :dqs b13 o 13:= by
  fin_cases o <;> exact receipt! Jj 0xa002710026ef1ffc8628009c400a3c7a7a608c0000100000df31b422800014000139fcc820c0000100000d52f6963000004000034a5c81cc800007393ee50909130000040000365d1dd8e0000100000bbeee7d30001540011cda1fa8ce0000100000af6eb54400000400002b16ddd1000001000009c7a287
private theorem cover {b:fO} (rows : ∀ o:Fin 13,∀ j:Fin 5,dqs b o (j.val+9))
    (hc:originCount b=13) (hs :stopCount b=14) (hf :afterFree b=8) :
    ∀ o∈origins b,∀ j∈stops b,afterFree b<j→dqs b o j:= by
  intro o ho j hj hfree
  have ho' : o<13:=hc ▸ Finset.mem_range.mp ho
  have hj' : j<14 :=hs ▸ Finset.mem_range.mp hj
  have hfree' : 8<j:=hf ▸ hfree
  let i:Fin 5:=⟨j-9,by omega⟩
  have hi:i.val+9=j:= by dsimp [i]; omega
  exact hi ▸ rows ⟨o,ho'⟩ i
theorem proof :q5oHm3d.c3:= by
  intro b hb
  have hl:b.val<14 :=b.isLt
  have he :b.val=12∨b.val=13:= by omega
  rcases he.imp (fun h=>show b=b12 from Fin.ext h)
      (fun h=>show b=b13 from Fin.ext h) with rfl | rfl
  · exact cover (fun o j=> by fin_cases j <;> first | exact r12_9 o | exact r12_10 o | exact r12_11 o | exact r12_12 o | exact r12_13 o) rfl rfl rfl
  · exact cover (fun o j=> by fin_cases j <;> first | exact r13_9 o | exact r13_10 o | exact r13_11 o | exact r13_12 o | exact r13_13 o) rfl rfl rfl
end P5_7_2_3Q723
end
section
set_option autoImplicit true
namespace qgZaXVc
theorem proof :qJkiHnb.c3:=P5_7_2_3Q723.proof
end qgZaXVc
end
