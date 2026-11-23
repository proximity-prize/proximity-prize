import ProximityPrize.SubmissionLower.Z8rcaBc
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.ZQGI7be
import ProximityPrize.SubmissionLower.ZaOaNGc
import ProximityPrize.SubmissionLower.ZVZMqYa
import ProximityPrize.SubmissionLower.ZqtxWkc
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q49VXnc
noncomputable section
open Polynomial Finset
open scoped Classical BigOperators
open P6 (K)
open q6nKpZc (Input)
open qCReOzb (Mark)

open q7F2qKe (originBudget eHB)
open qzVScmb (last)
open qPY5jQe (degree ordinateCap rate)
open qkgz7gb (UJ)
open akZ (yE ajz)
open cu (Jet rD)
open atc (bri bg3 bv9)
open private c2O from ProximityPrize.SubmissionLower.K
open private caps Ca d5P from ProximityPrize.SubmissionLower.ZPZNNwd
def c1 :Prop :=qziIa4d.c3
def c2 :Prop :=qPY5jQe.c3
private theorem witnessed {b u del M Γ F} (x : @Input b u del M Γ F)
    {T:Finset K} (hT:T⊆Γ) :UJ degree M.word T M.label F.scalar := by
  have hlo:=x.vo.1
  have hhi:=x.vo.2
  obtain ⟨hpos,hmax⟩:=Ca b
  have hp:0<M.iF.toNat := by omega
  have hd:M.iF.toNat≤2703:= by omega
  refine ⟨fun _ _ _ _ eq=>sub_left_inj.mp eq,F.distinct.mono hT,?_,?_,
    M.iF.toNat,hp,x.D,fun γ hγ=>x.residues γ (hT hγ)⟩
  · exact fun γ hγ=>(P6_7.aic F (hT hγ)).trans (Nat.add_le_add_left hd _)
  · intro γ hγ
    let m:=F.mark γ (hT hγ)
    exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
theorem of_children (tame :c1) (nonlinear :c2) :qCReOzb.c1 := by
  have local_hit :qPY5jQe.c2 :=
    qziIa4d.of_children qOj34lc.proof qJ69aaa.proof
      tame qU1uHGd.proof
  intro b _ u del M Γ F x h D hD hv hcap
  let slice (f :Jet) :=Γ.filter (Mark F f)
  let gH :=D.biUnion slice
  refine ⟨gH,?_,fun f hf γ hγ hm=>mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨hγ,hm⟩⟩⟩
  obtain ⟨he,hu,hfee⟩:=caps b
  have count (f :Jet) (hf :f∈D) : (slice f).card≤ rate (ordinateCap b)*yE f 2 := by
    obtain ⟨hi,_,huses,hseed,_⟩:=hD.factors f hf
    obtain ⟨hC,hF,hp⟩:=c2O hi (hv f hf) hseed
    have h₀:yE f 0=(f.coeff 0).natDegree :=
      (congrArg atc.jetDegree hC).symm.trans (bri _)
    have h₂:yE f 2= Qt.gY (f.coeff 0) := by
      change atc.gY f= _
      rw [← congrArg atc.gY hC,bg3]
      apply le_antisymm
      · exact Finset.sup_le fun j _=>(Qt.Qc _ _).mp le_rfl j
      · apply (Qt.Qc _ _).mpr
        intro j
        by_cases hj:j∈(f.coeff 0).support
        · exact Finset.le_sup (f := fun i=>((f.coeff 0).coeff i).totalDegree) hj
        · simp [notMem_support_iff.mp hj]
    have hind (j:Fin 3) :yE f j≤originBudget b (last b) j :=
      (single_le_sum (fun _ _=>Nat.zero_le _) hf).trans (hcap j)
    obtain ⟨j,i,hpos⟩:=huses
    have hpos' : 0<yE f 2 :=hpos.trans_le ((bv9 f _).mp le_rfl j i)
    rw [h₂]
    refine d5P qb3Ndfc.proof local_hit nonlinear qXKgtFd.proof
      b (witnessed x (filter_subset _ _)) hF hp (h₀ ▸ (hind 0).trans he)
        (h₂ ▸ hpos') (h₂ ▸ (hind 2).trans hu) ?_
    intro γ hγ
    have hz :=(mem_filter.mp hγ).2
    unfold Mark rD at hz
    rwa [← hC,eval₂_C] at hz
  calc
    gH.card ≤ ∑ f∈D,(slice f).card:=card_biUnion_le
    _ ≤ ∑ f∈D,rate (ordinateCap b)*yE f 2 :=sum_le_sum count
    _=rate (ordinateCap b)*ajz D 2 :=(mul_sum ..).symm
    _≤ rate (ordinateCap b)*originBudget b (last b) 2 :=Nat.mul_le_mul_left _ (hcap 2)
    _≤eHB b:=(Nat.le_add_left _ _).trans hfee
end
end q49VXnc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace q7cZjxe
noncomputable section
open Polynomial MvPolynomial Finset
open P6 (K p jG)
open P5_7_2 (A topDonors row)
open q7F2qKe (weakAgreement)
open q6nKpZc (TopPair)
open qCQTZAc (Weighted degreeBound cheapHeight FixedData ContainsFixed declared_le fixed_product)
open private ix ren weight_total weight_index weight_physical lift_ren from ProximityPrize.SubmissionLower.ZaOaNGc
open P5_7_1 (TopRow topLift topConjugate atTop)
open qaySLPd (SupportCaps orient topLabel)
open cu (L FX kr j9 jz)
open jA (mA bC ED jW)
abbrev rawTop {b u del M Γ F} (top : @TopPair u del M Γ F b) (e :Bool) :TopRow :=
  ren L[X] (top.raw 0 e)
theorem top_ne {b u del M Γ F} (top : @TopPair u del M Γ F b) (e :Bool) :
    rawTop top e≠0:= fun h=>top.nonzero 0 e ((ren L[X]).injective (h.trans (map_zero _).symm))
theorem top_caps {b u del M Γ F} (top : @TopPair u del M Γ F b) (e :Bool) :
    let t:=if e then (topDonors b).2 else (topDonors b).1
    SupportCaps t.shape.B t.shape.J t.YM t.shape.U (rawTop top e) ∧
    Weighted (131071+(row b).declaredHi)
      (t.shape.m*weakAgreement-1+(t.shape.B+t.shape.J)*(row b).declaredHi) (rawTop top e) := by
  obtain ⟨hB,hJ,hC,hU,hW⟩:=top.caps 0 e
  have support (a :Fin 4 →₀ ℕ) (ha :a∈(rawTop top e).support) :
      a.mapDomain ix∈(top.raw 0 e).support ∧
        (top.raw 0 e).coeff (a.mapDomain ix)=(rawTop top e).coeff a := by
    have hc:=coeff_rename_mapDomain ix (show Function.Injective ix from ix.injective) (rawTop top e) a
    change ((ren L[X]).symm (rawTop top e)).coeff (a.mapDomain ix)= _ at hc
    rw [(ren L[X]).symm_apply_apply] at hc
    exact ⟨mem_support_iff.mpr (hc ▸ mem_support_iff.mp ha),hc⟩
  constructor
  · intro a ha
    have hs :=(support a ha).1
    have h1 :=(le_weightedTotalDegree _ hs).trans hB
    have h2 :=(le_weightedTotalDegree _ hs).trans hJ
    rw [weight_total] at h1
    rw [weight_index] at h2
    have h3:=(monomial_le_degreeOf (some 2) hs).trans hC
    have h4 :=(monomial_le_degreeOf none hs).trans hU
    rw [show (some 2 :mA)=ix 3 from rfl,Finsupp.mapDomain_apply_of_injective ix.injective] at h3
    rw [show (none :mA)=ix 0 from rfl,Finsupp.mapDomain_apply_of_injective ix.injective] at h4
    exact ⟨h1,h2,h3,h4⟩
  · intro a ha
    obtain ⟨hm,hc⟩:=support a ha
    simpa only [hc,weight_physical,Nat.add_assoc] using hW _ hm
private theorem orient_raw {b u del M Γ F} (top : @TopPair u del M Γ F b)
    (i:Fin 2) (e :Bool) :orient i (rawTop top e)=ren L[X] (top.raw i e) := by
  fin_cases i
  · rfl
  · change topConjugate (rawTop top e)=ren L[X] (top.raw 1 e)
    rw [top.conjugate e]
    exact map_rename _ _ _
theorem top_zero {b u del} {M:jG u del} {Γ} {F:P1.bje A M Γ}
    (top:TopPair M F b) (i:Fin 2) (e :Bool) (γ:K) (hγ:γ∈Γ) :
    atTop (orient i (rawTop top e)) (topLabel i (M.label γ)) (F.scalar γ)=0:= by
  rw [orient_raw,atTop,← MvPolynomial.eval_map]
  change eval _ (topLift (ren L[X] (top.raw i e)))= _
  rw [lift_ren]
  change eval _ (rename ix.symm (bC (top.raw i e)))= _
  rw [eval_rename]
  let z :=M.label γ
  let S:=F.scalar γ
  have hv : (![jz (topLabel i z),kr S,kr S.derivative,kr (hasseDeriv 2 S)] ∘
      ix.symm)=ED (jz z^(p^i.val)) (jW (j9 S)) := by
    funext j
    obtain ⟨k,rfl⟩:=ix.surjective j
    rw [Function.comp_apply,ix.symm_apply_apply]
    fin_cases k
    · change jz (topLabel i z)=jz z^(p^i.val)
      fin_cases i
      · change jz (topLabel 0 z)=jz z^(p^(0:Fin 2).val)
        rw [Fin.val_zero,pow_zero,pow_one]
        rfl
      · change jz (topLabel 1 z)=jz z^(p^(1 :Fin 2).val)
        rw [Fin.val_one,pow_one,topLabel,ite_eq_right (by decide : (1 :Fin 2)≠0)]
        exact map_pow jz z p
    · change kr S=jA.qV (hasseDeriv 0 (j9 S))
      rw [hasseDeriv_zero']
      rfl
    · change jA.qV (j9 S.derivative) =
        jA.qV (hasseDeriv 1 (j9 S))
      rw [hasseDeriv_one']
      exact congrArg jA.qV (derivative_map S (algebraMap K L)).symm
    · change jA.qV (j9 (hasseDeriv 2 S)) =
        jA.qV (hasseDeriv 2 (j9 S))
      exact congrArg jA.qV (hasseDeriv_map (algebraMap K L) 2 S).symm
  rw [hv]
  exact top.zero i e γ hγ
theorem fixed_only {b u del M Γ F} (top : @TopPair u del M Γ F b)
    (i:Fin 2) (Q:MvPolynomial (Fin 4) FX) (hQ:Irreducible Q) (hpos :0<Q.degreeOf 3)
    (hc:Q∣topLift (orient i (rawTop top false)))
    (hs :Q∣topLift (orient i (rawTop top true))) :Q.degreeOf 0=0:= by
  let R:=(ren FX).symm Q
  have hdeg (j:Fin 4) :R.degreeOf (ix j)= Q.degreeOf j :=
    degreeOf_rename_of_injective ix.injective j
  have pull (e :Bool) (he :Q∣topLift (orient i (rawTop top e))) :
      R∣bC (top.raw i e) := by
    rw [orient_raw,lift_ren] at he
    simpa only [AlgEquiv.symm_apply_apply] using map_dvd (ren FX).symm he
  exact (hdeg 0).symm.trans (top.no_moving_top i R (hQ.map (ren FX).symm)
    (by change 0<R.degreeOf (ix 3); rw [hdeg]; exact hpos) (pull false hc) (pull true hs))
private theorem cheap_weight {b u del M Γ F} (top : @TopPair u del M Γ F b) :
    Weighted degreeBound cheapHeight (rawTop top false) := by
  let h:=(row b).declaredHi
  let t:=(topDonors b).1
  have ht:t.shape.m=64∧t.shape.B=87∧t.shape.J=27:= by
    dsimp [t,topDonors]
    split <;> decide
  have hc:=(top_caps top false).1
  have hw:=(top_caps top false).2
  simp only [Bool.false_eq_true,ite_false] at hc hw
  intro e he
  have hb:=(hc e he).1
  have hh:h≤2703:=declared_le b
  let a :=2703-h
  have hm:=Nat.mul_le_mul_left a (hb.trans_eq ht.2.1)
  have step (j:ℕ) (hj:j≤2) :
      degreeBound-j=(131071+h-j)+a := by dsimp [degreeBound,a]; omega
  have h1 :=hw e he
  change _+(131071+h)*e 1+(131071+h-1)*e 2+(131071+h-2)*e 3 ≤
    t.shape.m*weakAgreement-1+(t.shape.B+t.shape.J)*h at h1
  rw [ht.1,ht.2.1,ht.2.2] at h1
  change _+(131071+h)*e 1+(131071+h-1)*e 2+(131071+h-2)*e 3 ≤
    64*A-1+114*h at h1
  change _+(degreeBound-0)*e 1+(degreeBound-1)*e 2+(degreeBound-2)*e 3≤_
  rw [step 0 (by decide),step 1 (by decide),step 2 (by decide)]
  simp only [Nat.add_mul]
  rw [Nat.mul_add,Nat.mul_add] at hm
  change _≤64*A-1+114*2707
  dsimp [a] at hm ⊢
  omega
theorem cheap_caps {b u del M Γ F} (top : @TopPair u del M Γ F b) :
    SupportCaps 87 27 12 (topDonors b).1.shape.U (rawTop top false) := by
  have h:=(top_caps top false).1
  simp only [Bool.false_eq_true,ite_false] at h
  by_cases hb:b.val<7 <;> simpa only [topDonors,hb,ite_true,ite_false] using h
theorem fixed_of_pair {b u del M Γ F} (top : @TopPair u del M Γ F b) :
    ∃ B:TopRow,FixedData B∧ContainsFixed (rawTop top false) B :=
  fixed_product (top_ne top false) (cheap_caps top) (cheap_weight top)
end
end q7cZjxe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace q7cZjxe
noncomputable section
open Polynomial Finset
open scoped Classical
open P6 (K p)
open P5_7_2 (topDonors)
open q7F2qKe (originBudget)
open qzVScmb (aOm last)
open q6nKpZc (TopPair)
open qCReOzb (Mark LastCut)
open qCQTZAc (FixedData ContainsFixed Singular cap_small)
open P5_7_1 (TopRow topLift topConjugate atTop)
open qaySLPd (orient topLabel omitted pad)
open cu (FX Jet Equation aZ rD jz)
open pI (oU)
open bjF (view b2m)
open akZ (yE)
open private b0u from ProximityPrize.SubmissionLower.A3
open private aby from ProximityPrize.SubmissionLower.ZaOaNGc
open private separantCaps nonzero_seed from ProximityPrize.SubmissionLower.ZFKrBre
open private top_relation lift_conjugate conjugate_degree conjugate from ProximityPrize.SubmissionLower.ZXiQNLd
private theorem common_fixed {b u del M Γ F} (top : @TopPair u del M Γ F b)
    {f :Jet} {B:TopRow} {i:Fin 2}
    (hB:FixedData B) (hcontains :ContainsFixed (rawTop top false) B)
    (hf :Irreducible f) (hsep : ¬ f∣f.derivative) (hdep:0<(view (omitted i) f).natDegree)
    (hc:f∣pad f i 12 (rawTop top false))
    (hs :f∣pad f i (topDonors b).2.YM (rawTop top true)) :
    f∣pad f i 12 B:= by
  have cb (a) (ha :a∈(rawTop top false).support) :a 3≤12 :=
    (cheap_caps top a ha).2.2.1
  have sb (a) (ha :a∈(rawTop top true).support) :a 3≤(topDonors b).2.YM :=
    ((top_caps top true).1 a ha).2.2.1
  obtain ⟨Q,hQ,ht,hrel⟩:=top_relation hf hsep hdep (top_ne top false) cb hc
  apply (hrel (S:=B) (c' := 12) (fun a ha=>(hB.support a ha).2.2.1)).mpr
  have hdC:=(hrel cb).mp hc
  have hdS:=(hrel sb).mp hs
  have hfix :=fixed_only top i Q hQ ht hdC hdS
  fin_cases i
  · exact hcontains Q hQ ht hfix hdC
  · change Q∣topLift (topConjugate B)
    change Q∣topLift (topConjugate (rawTop top false)) at hdC
    rw [lift_conjugate] at hdC ⊢
    have hc' : conjugate.symm Q∣topLift (rawTop top false) := by
      simpa only [RingEquiv.symm_apply_apply] using map_dvd conjugate.symm hdC
    have h:=hcontains _ (hQ.map conjugate.symm) ((conjugate_degree Q 3).symm ▸ ht)
      ((conjugate_degree Q 0).trans hfix) hc'
    simpa only [RingEquiv.apply_symm_apply] using map_dvd conjugate h
private theorem cut_of_pad {b u del M Γ F} {gH :Finset K} {f g:Jet}
    (hp : ¬ f∣g) (hc:oU g (aOm b f))
    (hz : ∀ γ∈Γ,Mark (M:=M) (F:=F) f γ→Mark F g γ) :
    Nonempty (@LastCut u del M Γ F b gH f) :=
  ⟨⟨g,false,0,hp,hc,by simp,by simp,by simp,fun γ hγ h=>Or.inr (Or.inl (hz γ hγ h))⟩⟩
theorem proof :qCReOzb.c2 := by
  intro b _ u del M Γ F x h D top hD hvel hmass
  obtain ⟨B,hB,hcontains⟩:=fixed_of_pair top
  let gH :=Γ.filter (fun γ=>Singular B (M.label γ) (F.scalar γ))
  have hsub:gH⊆Γ:=filter_subset _ _
  refine ⟨gH,qLKC7de.proof B hB gH M.label F.scalar (F.distinct.mono hsub) (fun γ hγ =>
    ⟨scalar_le x (hsub hγ),(F.mark γ (hsub hγ)).scalar_fixed,(mem_filter.mp hγ).2⟩),?_⟩
  intro f hf
  obtain ⟨hi,hd,hseed,_,_⟩:=hD.factors f hf
  have individual (j:Fin 3) :yE f j≤originBudget b (last b) j :=
    (single_le_sum (f := fun g=>yE g j) (fun _ _=>Nat.zero_le _) hf).trans (hmass j)
  have hsmallV:f.natDegree<p:=(individual 1).trans_lt (cap_small b).1
  have hsmallSeed :yE f 2<p:=(individual 2).trans_lt (cap_small b).2
  let:CharP FX p:=charP_of_injective_ringHom jz.injective p
  let:CharP aZ p:=charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 2) FX) p
  let:CharP Equation p:=charP_of_injective_ringHom Polynomial.C_injective p
  have hproper :=b0u (A:=Equation) (q:=p) f (hvel f hf) hsmallV
  obtain ⟨j,hj⟩:=b2m f hseed
  let i:=omitted j
  have hdep:0<(view (omitted i) f).natDegree := by
    have he :omitted i=j:= by fin_cases j <;> decide
    simpa only [he] using hj
  let t:=(topDonors b).2
  obtain ⟨hc,hec⟩:=qT3dOZa.proof f i (rawTop top false) 87 27 12 _ (cheap_caps top)
  obtain ⟨hs,hes⟩:=qT3dOZa.proof f i (rawTop top true) t.shape.B t.shape.J
    t.YM t.shape.U (top_caps top true).1
  by_cases hpc:f∣pad f i 12 (rawTop top false)
  swap
  · exact cut_of_pad hpc (aby hc) (fun γ hγ hz=> by
      rw [Mark,hec _ _ hz,top_zero top i false γ hγ,mul_zero])
  by_cases hps :f∣pad f i t.YM (rawTop top true)
  swap
  · exact cut_of_pad hps hs (fun γ hγ hz=> by
      rw [Mark,hes _ _ hz,top_zero top i true γ hγ,mul_zero])
  have hdB:=common_fixed top hB hcontains hi hproper hdep hpc hps
  have hLift:=lift_of_anchor x h hi hd
  obtain ⟨_,heB⟩:=qT3dOZa.proof f i B 87 27 12 0 hB.support
  let T:=Γ.filter (fun γ=>γ∉gH∧Mark F f γ ∧ ¬ Mark F f.derivative γ)
  obtain ⟨r,hr,hline⟩:=line_of_fibres F f T (by
    intro γ hγ
    obtain ⟨hγ,hnot,hz,hv⟩:=mem_filter.mp hγ
    change rD f (M.label γ) (F.scalar γ)=0 at hz
    have hEval :=map_dvd (XY.vf (M.label γ) (F.scalar γ)) hdB
    change rD f (M.label γ) (F.scalar γ) ∣
      rD (pad f i 12 B) (M.label γ) (F.scalar γ) at hEval
    rw [hz,zero_dvd_iff,heB _ _ hz] at hEval
    have htwo: (2 :FX)≠0:= fun hz =>
      (by decide : ¬ p∣2) ((CharP.cast_eq_zero_iff FX p 2).mp hz)
    have hzero :=(mul_eq_zero.mp hEval).resolve_left (pow_ne_zero _ (mul_ne_zero htwo hv))
    have hregular :atTop (MvPolynomial.pderiv 3 (orient i B)) (topLabel i (M.label γ)) (F.scalar γ)≠0 :=
      fun he=>hnot (mem_filter.mpr ⟨hγ,⟨i,hzero,he⟩⟩)
    exact ⟨hv,qZ4UNdb.proof f B i _ _ hB.support hLift hsmallSeed
      (scalar_le x hγ) hdB hz hv hzero hregular⟩)
  refine ⟨⟨f.derivative,true,r,hproper,separantCaps f,fun _=>rfl,fun _=>hr,
    fun _=>nonzero_seed hseed,?_⟩⟩
  intro γ hγ hz
  by_cases hp:γ∈gH
  · exact Or.inl hp
  by_cases hv :Mark F f.derivative γ
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr ⟨rfl,hline γ (mem_filter.mpr ⟨hγ,hp,hz,hv⟩)⟩)
end
end q7cZjxe
end
