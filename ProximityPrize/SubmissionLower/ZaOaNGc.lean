import ProximityPrize.SubmissionLower.Zqop1Ec
import ProximityPrize.SubmissionLower.Zl6SIrc
import ProximityPrize.SubmissionLower.ZdSQxye
import ProximityPrize.SubmissionLower.ZXiQNLd
import ProximityPrize.SubmissionLower.Z0SAUab
set_option Elab.async false
open _root_ renaming Fin.sum_univ_three → zCj, Finsupp.mapDomain_apply_of_injective → zm3, Finsupp.optionElim_some → zX5, Finsupp.weight_eq_sum → z1K, Finsupp.weight_optionElim → zVB, Fintype.sum_option → zy6, Matrix.cons_val_zero → zbs, MvPolynomial.eval → zY9, Nat.add_le_add → z9f, Nat.eq_zero_of_le_zero → za7, Nat.mul_le_mul_right → ztf, Polynomial.derivative → zst, Polynomial.hasseDeriv → z75
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qCQTZAc
noncomputable section
open Polynomial MvPolynomial Finset

open P5_7_2 (topDonors row)
open q7F2qKe (TopPair weakAgreement)
open P5_7_1 (TopRow topLift)
open qaySLPd (SupportCaps)
open cu (L FX)
open jA (jK mA bC)
private abbrev ix :Fin 4 ≃ mA:=finSuccEquiv 3
private abbrev ren (R:Type*) [CommSemiring R] :=MvPolynomial.renameEquiv (R:=R) ix.symm
abbrev rawTop {b u del M Γ F} (top : @TopPair u del M Γ F b) (e :Bool) :TopRow :=
 ren L[X] (top.raw 0 e)
private theorem weight_total (a :Fin 4 →₀ ℕ) :
  (a.mapDomain ix).weight (fun v=>v.elim 0 (fun _=>1))=a 1+a 2+a 3:= by
 rw [z1K,zy6]
 simp [zCj,smul_eq_mul]
private theorem weight_index (a :Fin 4 →₀ ℕ) :
  (a.mapDomain ix).weight (fun v=>v.elim 0 Fin.val)=a 2+2*a 3:= by
 rw [z1K,zy6]
 simp [zCj,smul_eq_mul,
  Nat.mul_comm]
private theorem weight_physical (h:ℕ) (a :Fin 4 →₀ ℕ) :
   (a.mapDomain ix).sum (fun v n=>v.elim 0 (fun j=>(131071+h - j.val)*n)) =
     (131071+h)*a 1+(131071+h-1)*a 2+(131071+h-2)*a 3:= by
 rw [Finsupp.sum_fintype _ _ (by intro v; cases v <;> simp),zy6]
 simp [zCj]
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
    rw [show (some 2 :mA)=ix 3 from rfl,zm3 ix.injective] at h3
    rw [show (none :mA)=ix 0 from rfl,zm3 ix.injective] at h4
    exact ⟨h1,h2,h3,h4⟩
  · intro a ha
    obtain ⟨hm,hc⟩:=support a ha
    simpa only [hc,weight_physical,Nat.add_assoc] using hW _ hm
private theorem lift_ren (P:jK) :
  topLift (ren L[X] P)=ren FX (bC P) :=
 map_rename _ _ _
end
end qCQTZAc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qCQTZAc
noncomputable section
open Polynomial
open P5 (p)
open P5_7_2 (fO row)
open q7F2qKe (nV originBudget)
open qzVScmb (last)


open private bLI from ProximityPrize.SubmissionLower.ZdSQxye
theorem declared_le (b:fO) : (row b).declaredHi≤2703:=(bLI b).2
theorem cap_small (b:fO) :
  originBudget b (last b) 1<p∧originBudget b (last b) 2<p:= by
 fin_cases b <;> decide
private theorem shape_bound (b:fO) :
  let s :=(nV b 0).free
  s.m≤100∧s.B≤150∧s.J≤150:= by
 fin_cases b <;> decide


end
end qCQTZAc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qCQTZAc
noncomputable section
open Polynomial MvPolynomial Finset UniqueFactorizationMonoid
open P5_7_2 (topDonors)
open q7F2qKe (TopPair)
open P5_7_1 (TopRow topLift)
open qaySLPd (SupportCaps)
open cu (FX)
open private lift_injective degree_lift degree_dvd lift_factor support_dvd weights weight_exp flatten cSJ from ProximityPrize.SubmissionLower.ZXiQNLd
open scoped BigOperators
private abbrev Lifted:=MvPolynomial (Fin 4) FX
private theorem physical_weight (F:TopRow) (d W:ℕ) :
   Weighted d W F↔(flatten F).weightedTotalDegree
     (fun v=>v.elim 1 (weights d (d-1) (d-2)))≤W:= by
 rw [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
 constructor
 · intro h a ha
   have hcoeff : (F.coeff a.some).coeff (a none)≠0:= by
     rw [← cSJ,zX5]
     exact MvPolynomial.mem_support_iff.mp ha
   have hm:=MvPolynomial.mem_support_iff.mpr (fun hz=>hcoeff (by rw [hz,coeff_zero]))
   have hle :=Polynomial.le_natDegree_of_ne_zero hcoeff
   rw [← zX5 a,zVB,one_mul,weight_exp]
   have hh:=h a.some hm
   omega
 · intro h e he
   let a :=(F.coeff e).natDegree
   have hc: (F.coeff e).coeff a≠0 :=
     Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he)
   have hd:e.optionElim a∈(flatten F).support :=
     MvPolynomial.mem_support_iff.mpr (by rwa [cSJ])
   have hh:=h _ hd
   rw [zVB,one_mul,weight_exp] at hh
   omega
set_option backward.isDefEq.respectTransparency true in
theorem fixed_product {P:TopRow} {U:ℕ} (hP:P≠0)
    (hc:SupportCaps 87 27 12 U P) (hw:Weighted degreeBound cheapHeight P) :
    ∃ B:TopRow,FixedData B∧ContainsFixed P B:= by
  classical
  let:UniqueFactorizationMonoid FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid Lifted:=MvPolynomial.uniqueFactorizationMonoid (Fin 4)
  let:DecompositionMonoid Lifted:=inferInstance
  let _:StrongNormalizationMonoid TopRow :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let M:=normalizedFactors P
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
  have hdiv :B∣P :=
    (Finset.prod_dvd_prod_of_subset T M.toFinset id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hP).dvd)
  have hB:B≠0:=ne_zero_of_dvd_ne_zero hP hdiv
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
  · apply support_dvd hP hdiv
    · exact hc
    · apply za7 ((degreeOf_prod_le 0 T id).trans ?_)
      exact (Finset.sum_eq_zero fun F hF=>(hmem F hF).2.2).le
  · apply (physical_weight B _ _).mpr
    exact (weightedTotalDegree_le_of_dvd _ (_root_.map_dvd flatten hdiv)
      (fun hz=>hP (flatten.injective (hz.trans (map_zero _).symm)))).trans
        ((physical_weight _ _ _).mp hw)
  · intro Q hQ hTop hSeed hQdiv
    have hprod:=hQdiv.trans (_root_.map_dvd topLift (prod_normalizedFactors hP).symm.dvd)
    rw [map_multiset_prod] at hprod
    obtain ⟨F,hF,hQF⟩:=hQ.prime.exists_mem_multiset_map_dvd hprod
    have hFirr :=irreducible_of_normalized_factor F hF
    have hFne :topLift F≠0:=(map_ne_zero_iff topLift lift_injective).mpr hFirr.ne_zero
    have ht:=degree_dvd 3 hQF hFne
    rw [degree_lift] at ht
    have hFt:=hTop.trans_le ht
    have hFQ:=hQ.dvd_symm (lift_factor hFirr hFt).1 hQF
    have hs :=degree_dvd 0 hFQ hQ.ne_zero
    rw [degree_lift,hSeed] at hs
    have hFs :=za7 hs
    have hTF:F∈T :=
      Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hF,hFt,hFs⟩
    exact hQF.trans (_root_.map_dvd topLift (Finset.dvd_prod_of_mem id hTF))
theorem cheap_caps {b u del M Γ F} (top : @TopPair u del M Γ F b) :
  SupportCaps 87 27 12 (topDonors b).1.shape.U (rawTop top false) := by
 have h:=(top_caps top false).1
 simp only [Bool.false_eq_true,ite_false] at h
 by_cases hb:b.val<7 <;> simpa only [topDonors,hb,ite_true,ite_false] using h
end
end qCQTZAc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace qT3dOZa
noncomputable section
open Polynomial Finset
open P5 (K)
open cu (L FX Equation Jet kr yq qD jz rD)
open vq (Dx aYD apZ bzc aKe flatten D6 separant alU aNA)
open Qv (S4 lX)
open P5_7_1 (TopRow topLift atTop)
open qaySLPd (c1 SupportCaps orient pad topLabel)
private abbrev ev :=XY.vf
private theorem dx_inner (z :K) (S:K[X]) (g:Equation) :
  Dx (yq g z S) =
   yq (lX g) z S+kr S.derivative*yq g.derivative z S:= by
 have hx :vq.vf z S (D6 (flatten g)) =
   yq (lX g) z S:= by
  have h:flatten (lX g)=D6 (flatten g) :=
   (MvPolynomial.optionEquivLeft FX (Fin 2)).symm_apply_apply _
  rw [← alU,h]
 have h:=aKe z S (flatten g)
 change Dx (vq.vf z S (flatten g)) =
  vq.vf z S (D6 (flatten g)) +
   kr S.derivative*vq.vf z S (separant (flatten g)) at h
 simpa only [alU,hx,aNA] using h
private theorem liftAdd {d:Equation→Equation} (h0:d 0=0)
  (ha : ∀ a b,d (a+b)=d a+d b) (f g:Jet) :
  S4 d (f+g)=S4 d f+S4 d g:= by
 ext n
 simp only [coeffLift h0,coeff_add,ha]
private theorem liftMono {d:Equation→Equation} (h0:d 0=0) (n:ℕ) (q:Equation) :
  S4 d (monomial n q)=monomial n (d q) := by
 apply Polynomial.ext
 intro m
 simp only [coeffLift h0,coeff_monomial]
 split <;> simp_all
private theorem ev_mono (z :K) (S:K[X]) (n:ℕ) (q:Equation) :
  ev z S (monomial n q)=yq q z S*kr S.derivative^n :=
 eval₂_monomial (eval₂RingHom (qD z) (kr S)) (kr S.derivative)
private theorem dx_outer (z :K) (S:K[X]) (f :Jet) :
    Dx (ev z S f)=ev z S (S4 lX f) +
      kr S.derivative*ev z S (S4 zst f) +
      kr S.derivative.derivative*ev z S f.derivative := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have ha (a b:Equation) :lX (a+b) =
        lX a+lX b:= by simp only [lX,map_add]
    simp only [map_add,hf,hg,liftAdd phys_zero ha,
      liftAdd derivative_zero (fun a b:Equation=>map_add zst a b)]
    ring
  | monomial n q =>
    have he :yq (q*(n:Equation)) z S=yq q z S*(n:FX) := by
      change (eval₂RingHom (qD z) (kr S)) (q*(n:Equation))= _
      rw [map_mul,map_natCast] <;> rfl
    rw [ev_mono,apZ,dx_inner,bzc,aYD,liftMono phys_zero,
      liftMono derivative_zero,derivative_monomial]
    simp only [ev_mono,he]
    ring
private theorem second (S:K[X]) :
  kr S.derivative.derivative=2*kr (z75 2 S) := by
 have h:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=K) 2) S
 change (2 :ℕ)•z75 2 S=S.derivative.derivative at h
 let a :K[X] →+* FX:=(algebraMap L[X] FX).comp (Polynomial.mapRingHom (algebraMap K L))
 change a S.derivative.derivative=2*a (z75 2 S)
 rw [← h,map_nsmul,two_nsmul,two_mul]
private theorem dcQ (n:ℕ) (z :K) (i:Fin 2) :
   ![jz z,jz z^n] i =
     jz (if i=0 then z else z^n) := by
 by_cases hi:i=0
 · rw [ite_eq_left hi,hi,zbs]
 · rw [ite_eq_right hi,Fin.eq_one_of_ne_zero i hi,Matrix.cons_val_one,zbs,map_pow]
private theorem evalSeed (v :Fin 2→FX) (S:K[X]) (i:Fin 2) :
  eval₂RingHom (eval₂RingHom (zY9 v) (kr S)) (kr S.derivative)
   (C (C (MvPolynomial.X i)))=v i:= by
 simp only [coe_eval₂RingHom,eval₂_C,MvPolynomial.eval_X]
private theorem ev_seed (z :K) (S:K[X]) (i:Fin 2) :
  ev z S (C (C (MvPolynomial.X i)))=jz (topLabel i z) := by
 calc
  _ = ![jz z,jz z^K1.p] i:=evalSeed _ S i
  _=jz (if i=0 then z else z^K1.p) :=dcQ K1.p z i
  _ = _:= by rw [topLabel,P0.twist,frobenius_def]
private theorem ev_scalar (z :K) (S:K[X]) (a :FX) :
  ev z S (algebraMap FX Jet a)=a := by
 change ev z S (C (C (MvPolynomial.C a)))= _
 simp only [ XY.vf,coe_eval₂RingHom,eval₂_C,qD,MvPolynomial.eval_C]
private theorem ev_ord (z :K) (S:K[X]) :ev z S (C (Polynomial.X:Equation))=kr S:= by
 simp only [ XY.vf,coe_eval₂RingHom,eval₂_C,eval₂_X]
private theorem ev_vel (z :K) (S:K[X]) :ev z S (Polynomial.X:Jet)=kr S.derivative := by
 simp only [ XY.vf,coe_eval₂RingHom,eval₂_X]
private theorem padEval (f :Jet) (i:Fin 2) (T:TopRow) (B J C U:ℕ)
    (h:SupportCaps B J C U T) (z :K) (S:K[X]) (hf :rD f z S=0) :
    rD (pad f i C T) z S =
      (2*rD f.derivative z S)^C*atTop (orient i T) (topLabel i z) S:= by
  let w:=kr (z75 2 S)
  let d:=2*ev z S f.derivative
  change ev z S f=0 at hf
  change ev z S (pad f i C T)=d^C*atTop (orient i T) (topLabel i z) S
  have hn : -(ev z S (S4 lX f) +
      kr S.derivative*ev z S (S4 zst f))=d*w:= by
    have hd:=dx_outer z S f
    rw [hf,map_zero,second] at hd
    dsimp [d,w]
    linear_combination -hd.symm
  have ht:atTop (orient i T) (topLabel i z) S =
      zY9 ![jz (topLabel i z),kr S,kr S.derivative,w]
        (topLift (orient i T)) := by
    symm
    apply MvPolynomial.eval_map
  rw [ht,MvPolynomial.eval_eq',Finset.mul_sum]
  simp only [pad,map_sum,map_mul,map_pow,map_neg,map_add,map_ofNat,
    ev_scalar,ev_seed,ev_ord,ev_vel,hn,Fin.prod_univ_four]
  apply Finset.sum_congr rfl
  intro e he
  have hc:=(h e (lift_support he)).2.2.1
  have hp:d^(e 3)*d^(C-e 3)=d^C:= by rw [← pow_add,Nat.add_sub_of_le hc]
  change _ *_ *_ *_ *(d*w)^(e 3)*d^(C-e 3) =
    d^C*((topLift (orient i T)).coeff e *
      (jz (topLabel i z)^e 0*kr S^e 1*kr S.derivative^e 2*w^e 3))
  rw [mul_pow,← hp]
  ac_rfl
theorem proof :c1 := by
 intro f i T B J C U h
 exact ⟨padCaps f i T B J C U h,padEval f i T B J C U h⟩
end
end qT3dOZa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qCQTZAc
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K p twist)
open P5_7_2 (fO topDonors)
open q7F2qKe (akj)
open qzVScmb (aOm)
open P5_7_1 (TopRow atTop)
open qaySLPd (orient topLabel pad SupportCaps ConstantFibre)
open cu (Jet rD)
open pI (oU)

open akZ (yE)






def c1 :Prop :=
  ∀ (B:TopRow),FixedData B → ∀ (T:Finset K) (z :K→K) (S:K→K[X]),
    Set.InjOn S (T:Set K) →
    (∀ γ∈T,(S γ).natDegree≤degreeBound∧(S γ).map twist=S γ∧Singular B (z γ) (S γ)) →
    T.card≤akj
def c2 :Prop :=
  ∀ (f :Jet) (B:TopRow) (i:Fin 2) (z :K) (S:K[X]),
    SupportCaps 87 27 12 0 B→LiftAt degreeBound liftHeight f →
    yE f 2<p→S.natDegree≤degreeBound →
    f∣pad f i 12 B→ rD f z S=0→ rD f.derivative z S≠0 →
    atTop (orient i B) (topLabel i z) S=0 →
    atTop (MvPolynomial.pderiv 3 (orient i B)) (topLabel i z) S≠0 →
    ConstantFibre f z S
private theorem aby {b:fO} {f g:Jet}
   (h:oU g ⟨0,87+12*(yE f 0-1),27+12*(yE f 1-1),
     (topDonors b).1.shape.U+12*yE f 2⟩) :
   oU g (aOm b f) := by
 let t:=(topDonors b).2
 have guard :87≤t.shape.B∧27≤t.shape.J ∧
     (topDonors b).1.shape.U≤t.shape.U∧12≤t.YM:= by
   dsimp [t,topDonors]
   split <;> decide
 intro j k hj
 obtain ⟨hB,hJ,hU⟩:=h j k hj
 exact ⟨hB.trans (z9f guard.1 (ztf _ guard.2.2.2)),
   hJ.trans (z9f guard.2.1 (ztf _ guard.2.2.2)),
   hU.trans (z9f guard.2.2.1 (ztf _ guard.2.2.2))⟩
end
end qCQTZAc
end
