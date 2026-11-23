import ProximityPrize.SubmissionLower.Z9a2MVc
import ProximityPrize.SubmissionLower.ZBgX9Tc
import ProximityPrize.SubmissionLower.ZqtxWkc
import ProximityPrize.SubmissionLower.ZXLxXWd
set_option Elab.async false
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
namespace q3sIXNd
noncomputable section
open Polynomial

open P6_7_3 (degree)


open P5_7_1 (TopRow topLift)
open qaySLPd (SupportCaps)
abbrev topBudget:ℕ:=64*P5_7.midAgreement-1+114*P6_7_3.hi
def Weight (B:TopRow) (W:ℕ) :Prop :=
  ∀ e∈B.support,(B.coeff e).natDegree+degree*e 1 +
    (degree-1)*e 2+(degree-2)*e 3≤W
structure FixedData (B:TopRow) :Prop where
  ne :B≠0
  squarefree :Squarefree (topLift B)
  support :SupportCaps 87 27 12 0 B
  weight:Weight B topBudget
end
end q3sIXNd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q3sIXNd
noncomputable section
open Polynomial MvPolynomial Finset UniqueFactorizationMonoid
open P6_7_3 (TopPair Input degree emz)
open P5_7_1 (TopRow topLift topConjugate)
open qaySLPd (omitted pad)
open cu (FX Jet)
open bjF (view)
open private lift_injective degree_lift degree_dvd lift_factor support_dvd flatten cSJ weights weight_exp from ProximityPrize.SubmissionLower.ZXiQNLd
open private top_relation lift_conjugate conjugate_degree conjugate TopBound from ProximityPrize.SubmissionLower.ZXiQNLd
private abbrev Lifted:=MvPolynomial (Fin 4) FX
private theorem physical_weight (F:TopRow) (W:ℕ) :
    Weight F W↔(flatten F).weightedTotalDegree
      (fun v=>v.elim 1 (weights degree (degree-1) (degree-2)))≤W:= by
  rw [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
  constructor
  · intro h d hd
    have hcoeff : (F.coeff d.some).coeff (d none)≠0:= by
      rw [← cSJ,Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hd
    have hm:=MvPolynomial.mem_support_iff.mpr (fun hz=>hcoeff (by rw [hz,coeff_zero]))
    have hle :=Polynomial.le_natDegree_of_ne_zero hcoeff
    rw [← Finsupp.optionElim_some d,Finsupp.weight_optionElim,one_mul,weight_exp]
    have hh:=h d.some hm
    omega
  · intro h e he
    let a :=(F.coeff e).natDegree
    have hc: (F.coeff e).coeff a≠0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he)
    have hd:e.optionElim a∈(flatten F).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [cSJ])
    have hh:=h _ hd
    rw [Finsupp.weight_optionElim,one_mul,weight_exp] at hh
    omega
private theorem cheap_weight {x :Input} (top:TopPair x) :Weight top.cheap topBudget:= by
  intro e he
  obtain ⟨hb,_,_,_,hw⟩:=top.cheap_caps e he
  have hh:x.h≤2534 :=(emz x).2
  let d:=e 1+e 2+e 3
  have hm:=Nat.mul_le_mul_left (2534-x.h) (show d≤87 from hb)
  have hdeg:133605*d=(131071+x.h)*d+(2534-x.h)*d:= by
    rw [← Nat.add_mul,show 131071+x.h+(2534-x.h)=133605 by omega]
  change (top.cheap.coeff e).natDegree+133605*e 1+133604*e 2+133603*e 3≤11792235
  change (top.cheap.coeff e).natDegree+(131071+x.h)*d ≤
    11503359+114*x.h+e 2+2*e 3 at hw
  change 133605*(e 1+e 2+e 3)= _ at hdeg
  omega
set_option backward.isDefEq.respectTransparency true in
theorem fixed_product {x :Input} (top:TopPair x) :
    ∃ B:TopRow,FixedData B ∧
      (∀ Q:MvPolynomial (Fin 4) FX,Irreducible Q→0<Q.degreeOf 3 →
        Q.degreeOf 0=0→Q∣topLift top.cheap→Q∣topLift B) := by
  classical
  let:UniqueFactorizationMonoid FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid Lifted:=MvPolynomial.uniqueFactorizationMonoid (Fin 4)
  let:DecompositionMonoid Lifted:=inferInstance
  let _:StrongNormalizationMonoid TopRow :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let M:=normalizedFactors top.cheap
  let T:=M.toFinset.filter fun F=>0<F.degreeOf 3∧F.degreeOf 0=0
  let B := ∏ F∈T,F
  have hmem (F:TopRow) (hF:F∈T) :
      F∈M∧0<F.degreeOf 3∧F.degreeOf 0=0:= by
    obtain ⟨hm,ht⟩:=Finset.mem_filter.mp hF
    exact ⟨Multiset.mem_toFinset.mp hm,ht⟩
  have hirr (F:TopRow) (hF:F∈T) :Irreducible F :=
    irreducible_of_normalized_factor F (hmem F hF).1
  have hloc (F:TopRow) (hF:F∈T) :=
    lift_factor (hirr F hF) (hmem F hF).2.1
  have hdiv :B∣top.cheap :=
    (Finset.prod_dvd_prod_of_subset T M.toFinset id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors top.cheap_ne).dvd)
  have hB:B≠0:=ne_zero_of_dvd_ne_zero top.cheap_ne hdiv
  refine ⟨B,⟨hB,?_,?_,?_⟩,?_⟩
  · rw [show B = ∏ F∈T,F from rfl,map_prod]
    refine Finset.squarefree_prod_of_pairwise_isCoprime
      (R:=Lifted) (s :=T) (f :=topLift) ?_ ?_
    · intro F hF G hG hne
      apply (hloc F hF).1.isRelPrime_iff_not_dvd.mpr
      intro h
      have ha :=(hirr F hF).associated_of_dvd (hirr G hG) ((hloc F hF).2 G h)
      exact hne (mem_normalizedFactors_eq_of_associated (hmem F hF).1 (hmem G hG).1 ha)
    · exact fun F hF=>(hloc F hF).1.squarefree
  · apply support_dvd top.cheap_ne hdiv
    · exact fun e he=>⟨(top.cheap_caps e he).1,(top.cheap_caps e he).2.1,
        (top.cheap_caps e he).2.2.1,(top.cheap_caps e he).2.2.2.1⟩
    · apply Nat.eq_zero_of_le_zero ((degreeOf_prod_le 0 T id).trans ?_)
      exact (Finset.sum_eq_zero fun F hF=>(hmem F hF).2.2).le
  · apply (physical_weight B _).mpr
    exact (weightedTotalDegree_le_of_dvd _ (_root_.map_dvd flatten hdiv)
      (fun hz=>top.cheap_ne (flatten.injective (hz.trans (map_zero _).symm)))).trans
        ((physical_weight _ _).mp (cheap_weight top))
  · intro Q hQ hTop hSeed hQdiv
    have hP:=hQdiv.trans (_root_.map_dvd topLift (prod_normalizedFactors top.cheap_ne).symm.dvd)
    rw [map_multiset_prod] at hP
    obtain ⟨F,hF,hQF⟩:=hQ.prime.exists_mem_multiset_map_dvd hP
    have hFirr :=irreducible_of_normalized_factor F hF
    have hFne :topLift F≠0:=(map_ne_zero_iff topLift lift_injective).mpr hFirr.ne_zero
    have ht:=degree_dvd 3 hQF hFne
    rw [degree_lift] at ht
    have hFt:=hTop.trans_le ht
    have hFQ:=hQ.dvd_symm (lift_factor hFirr hFt).1 hQF
    have hs :=degree_dvd 0 hFQ hQ.ne_zero
    rw [degree_lift,hSeed] at hs
    have hFs :=Nat.eq_zero_of_le_zero hs
    have hTF:F∈T :=
      Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hF,hFt,hFs⟩
    exact hQF.trans (_root_.map_dvd topLift (Finset.dvd_prod_of_mem id hTF))
theorem fixed_contraction {x :Input} (top:TopPair x) {B:TopRow} (hB:FixedData B)
    (hcontains : ∀ Q:Lifted,Irreducible Q→0<Q.degreeOf 3 →
      Q.degreeOf 0=0→Q∣topLift top.cheap→Q∣topLift B)
    {f :Jet} {i:Fin 2} (hf :Irreducible f) (hsep : ¬ f∣f.derivative)
    (hdep:0<(view (omitted i) f).natDegree)
    (hc:f∣pad f i 12 top.cheap) (hs :f∣pad f i 19 top.strong) :
    f∣pad f i 12 B:= by
  have cb:TopBound 12 top.cheap:= fun a ha=>(top.cheap_caps a ha).2.2.1
  have sb:TopBound 19 top.strong:= fun a ha=>(top.strong_caps a ha).2.2.1
  obtain ⟨Q,hQ,ht,hrel⟩:=top_relation hf hsep hdep top.cheap_ne cb hc
  apply (hrel (S:=B) (c' := 12) (fun a ha=>(hB.support a ha).2.2.1)).mpr
  have hdC:=(hrel cb).mp hc
  have hdS:=(hrel sb).mp hs
  fin_cases i
  · exact hcontains Q hQ ht (top.no_moving Q hQ ht hdC hdS) hdC
  · change Q∣topLift (topConjugate B)
    rw [lift_conjugate]
    have undo (S:TopRow) (hS:Q∣topLift (topConjugate S)) :
        conjugate.symm Q∣topLift S:= by
      rw [lift_conjugate] at hS
      simpa only [RingEquiv.symm_apply_apply] using map_dvd conjugate.symm hS
    have hQ' := hQ.map conjugate.symm
    have ht' : 0<(conjugate.symm Q).degreeOf 3:=(conjugate_degree Q 3).symm ▸ ht
    have hc' := undo top.cheap hdC
    have hfix :=top.no_moving _ hQ' ht' hc' (undo top.strong hdS)
    simpa only [RingEquiv.apply_symm_apply] using map_dvd conjugate (hcontains _ hQ' ht' hfix hc')
end
end q3sIXNd
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qMEgcrb
noncomputable section
open Polynomial Finset
open P6 (K p)
open P6_7_3
open qFOgTpd
open q3sIXNd
open P5_7_1 (TopRow TopCaps atTop)
open qaySLPd (SupportCaps orient omitted pad topLabel)
open cu (FX Jet Equation rD jz)
open pI (oU)
open bjF (view b2m)
open scoped Classical
open private b0u from ProximityPrize.SubmissionLower.A3
open private separantCaps nonzero_seed from ProximityPrize.SubmissionLower.ZFKrBre
private theorem HE {B:TopRow} (hB:FixedData B) :
    qCQTZAc.Weighted qCQTZAc.degreeBound qCQTZAc.cheapHeight B:= by
  intro e he
  have h1 :=hB.weight e he
  have h2 :=(hB.support e he).1
  change (B.coeff e).natDegree+133605*e 1+133604*e 2+133603*e 3≤11792235 at h1
  change (B.coeff e).natDegree+133774*e 1+133773*e 2+133772*e 3≤11811957
  omega
private theorem deg_le {x :Input} {γ:K} (hγ:γ∈x.Γ) :
    (x.F.scalar γ).natDegree≤qCQTZAc.degreeBound :=
  (P6_7.aic x.F hγ).trans (Nat.add_le_add_left ((emz x).2.trans (by decide)) 131071)
private theorem supportOfTopCaps {h m B J C U:ℕ} {T:TopRow}
    (hT:TopCaps h m B J C U T) :SupportCaps B J C U T :=
  fun e he=>⟨(hT e he).1,(hT e he).2.1,(hT e he).2.2.1,(hT e he).2.2.2.1⟩
private theorem colour {x :Input} (t:TopPair x) (i:Fin 2) (γ:K) (hγ:γ∈x.Γ) :
    atTop (orient i t.cheap) (topLabel i (x.M.label γ)) (x.F.scalar γ)=0 ∧
    atTop (orient i t.strong) (topLabel i (x.M.label γ)) (x.F.scalar γ)=0:= by
  obtain ⟨hc,hs,hc',hs'⟩:=t.necessary γ hγ
  fin_cases i
  · simpa [orient,topLabel] using And.intro hc hs
  · simpa [orient,topLabel] using And.intro hc' hs'
private theorem aby {f g:Jet}
    (h:oU g ⟨0,87+12*(wD f 0-1),27+12*(wD f 1-1),640+12*wD f 2⟩) :
    oU g (aOm f) := by
  intro j k hj
  obtain ⟨hb,hv,hu⟩:=h j k hj
  change k+j≤164+19*(wD f 0-1)∧j≤50+19*(wD f 1-1) ∧
    ((g.coeff j).coeff k).totalDegree≤3037+19*wD f 2
  change k+j≤87+12*(wD f 0-1) at hb
  change j≤27+12*(wD f 1-1) at hv
  change ((g.coeff j).coeff k).totalDegree≤640+12*wD f 2 at hu
  omega
private theorem cutOfPad {x :Input} {gH :Finset K} {f g:Jet}
    (hp : ¬ f∣g) (hc:oU g (aOm f))
    (hz : ∀ γ∈x.Γ,Mark x f γ→Mark x g γ) :Nonempty (LastCut x gH f) :=
  ⟨⟨g,hp,false,0,hc,by simp,by simp,by simp,fun γ hγ h=>Or.inr (Or.inl (hz γ hγ h))⟩⟩
private theorem ref_lift {x :Input} {P:Poles x} (R:Reference x P) {f :Jet}
    (hf :Irreducible f) (hd:f∣DP.U4 R.raw) :
    qCQTZAc.LiftAt qCQTZAc.degreeBound qCQTZAc.liftHeight f := by
  refine qKVjhPa.lift_of_raw (emz x).2 R.nonzero (fun j i a e hc => ?_) hf hd
  have hamb:R.raw∈DP.Aw x.h anchor.free (cutoff anchor.free) :=R.mem.1.1
  have hel:DP.awN x.h anchor.free (cutoff anchor.free) j i a e := by
    by_contra hn
    exact hc (hamb j i a e hn)
  exact ⟨hel.1,hel.2.2.2⟩
theorem proof :qFOgTpd.c2 := by
  intro x P R top D hD hvel hmass
  obtain ⟨B,hB,hcontains⟩:=fixed_product top
  let gH :=x.Γ.filter (fun γ=>qCQTZAc.Singular B (x.M.label γ) (x.F.scalar γ))
  have hsub:gH⊆x.Γ:=filter_subset _ _
  refine ⟨gH,(qLKC7de.proof B ⟨hB.ne,hB.squarefree,hB.support,HE hB⟩ gH
    x.M.label x.F.scalar (x.F.distinct.mono hsub) (fun γ hγ=>⟨deg_le (hsub hγ),
      (x.F.mark γ (hsub hγ)).scalar_fixed,(mem_filter.mp hγ).2⟩)).trans (by decide),?_⟩
  intro f hf
  obtain ⟨hi,hd,hseed,_,_⟩:=hD.factors f hf
  have individual (j:Fin 3) :wD f j≤ introCap last j :=
    (single_le_sum (f := fun g=>wD g j) (fun _ _=>Nat.zero_le _) hf).trans (hmass j)
  have hsmallV:f.natDegree<p:=(individual 1).trans_lt (by decide)
  have hsmallSeed :wD f 2<p:=(individual 2).trans_lt (by decide)
  let:CharP FX p:=charP_of_injective_ringHom jz.injective p
  let:CharP (cu.aZ) p:=charP_of_injective_ringHom
    (MvPolynomial.C_injective (Fin 2) FX) p
  let:CharP Equation p:=charP_of_injective_ringHom Polynomial.C_injective p
  have hproper :=b0u (A:=Equation) (q:=p) f (hvel f hf) hsmallV
  obtain ⟨j,hj⟩:=b2m f hseed
  let i:=omitted j
  have hdep:0<(view (omitted i) f).natDegree := by
    have he :omitted i=j:= by fin_cases j <;> decide
    simpa only [he] using hj
  obtain ⟨hc,hec⟩:=qT3dOZa.proof f i top.cheap 87 27 12 640 (supportOfTopCaps top.cheap_caps)
  obtain ⟨hs,hes⟩:=qT3dOZa.proof f i top.strong 164 50 19 3037 (supportOfTopCaps top.strong_caps)
  by_cases hpc:f∣pad f i 12 top.cheap
  swap
  · exact cutOfPad hpc (aby hc) (fun γ hγ hz=> by
      rw [Mark,hec _ _ hz,(colour top i γ hγ).1,mul_zero])
  by_cases hps :f∣pad f i 19 top.strong
  swap
  · exact cutOfPad hps hs (fun γ hγ hz=> by
      rw [Mark,hes _ _ hz,(colour top i γ hγ).2,mul_zero])
  have hdB:=fixed_contraction top hB hcontains hi hproper hdep hpc hps
  have hLift:=ref_lift R hi hd
  obtain ⟨_,heB⟩:=qT3dOZa.proof f i B 87 27 12 0 hB.support
  let T:=x.Γ.filter (fun γ=>γ∉gH∧Mark x f γ ∧ ¬ Mark x f.derivative γ)
  obtain ⟨row,hr,hline⟩:=qKVjhPa.line_of_scalars x.M.label x.F.scalar f T (by
    intro γ hγ
    obtain ⟨hγ,hnot,hz,hv⟩:=mem_filter.mp hγ
    change rD f (x.M.label γ) (x.F.scalar γ)=0 at hz
    have hEval :=map_dvd (XY.vf (x.M.label γ) (x.F.scalar γ)) hdB
    change rD f (x.M.label γ) (x.F.scalar γ) ∣
      rD (pad f i 12 B) (x.M.label γ) (x.F.scalar γ) at hEval
    rw [hz,zero_dvd_iff,heB _ _ hz] at hEval
    have htwo: (2 :FX)≠0:= fun hz =>
      (by decide : ¬ p∣2) ((CharP.cast_eq_zero_iff FX p 2).mp hz)
    have hzero :=(mul_eq_zero.mp hEval).resolve_left (pow_ne_zero _ (mul_ne_zero htwo hv))
    have hregular :atTop (MvPolynomial.pderiv 3 (orient i B))
        (topLabel i (x.M.label γ)) (x.F.scalar γ)≠0 :=
      fun he=>hnot (mem_filter.mpr ⟨hγ,⟨i,hzero,he⟩⟩)
    exact ⟨hv,qZ4UNdb.proof f B i _ _ hB.support hLift hsmallSeed
      (deg_le hγ) hdB hz hv hzero hregular⟩)
  refine ⟨⟨f.derivative,hproper,true,row,separantCaps f,fun _=>rfl,
    fun _=>hr,fun _=>nonzero_seed hseed,?_⟩⟩
  intro γ hγ hz
  by_cases hp:γ∈gH
  · exact Or.inl hp
  by_cases hv :Mark x f.derivative γ
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr ⟨rfl,hline γ (mem_filter.mpr ⟨hγ,hp,hz,hv⟩)⟩)
end
end qMEgcrb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qxjPa5a
theorem proof :qFOgTpd.c3:= fun x f g hj hu _ hc =>
  qXLxXWd.count (D:=P6_7_3.degree) (by decide) (by decide) (by decide) (by decide) x.F
    (fun _ hγ=>(P6_7.aic x.F hγ).trans (Nat.add_le_add_left (P6_7_3.emz x).2 _))
    f g hj hu hc
end qxjPa5a
end
