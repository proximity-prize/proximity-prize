import ProximityPrize.SubmissionLower.ZQTNHBe
set_option Elab.async false
section
namespace q9uVqha
noncomputable section
open Polynomial Finset qLXroAb
open P5 (K p)
open cu (L)
open P5_7_7 (phys)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open scoped WithZero
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
def c1 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet Cq z S),3≤F.d→F.d<p→Nonempty (Generic F)
variable {F:Sheet Cq z S}
def c2 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]} {F:Sheet Cq z S}
    (V:Variation F) (G:Generic F) (γ:K) (hγ:γ∈V.marks),
    Nonempty (MarkReduction G γ (V.Bp hγ))
def c3:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]} {F:Sheet Cq z S}
    (G:Generic F) (γ:K) (hγ:γ∈F.marks),
    ringKrullDim (MvPolynomial (Fin 4) L ⧸ G.RS γ hγ)≤2
def c4 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]} {F:Sheet Cq z S}
    (V:Variation F) (G:Generic F),
    (∀ γ (hγ:γ∈V.marks),ringKrullDim (MvPolynomial (Fin 4) L ⧸
      G.RS γ (V.Bp hγ))≤2) →
    ∃ a b:Fin 4→L,G.form a≠0∧G.deriv (G.form b/G.form a)≠0 ∧
      ∀ γ (hγ:γ∈V.marks),GraphCut (G.RS γ (V.Bp hγ)) a b ∧
        linear (C:L →+* L[X]) a (markJet S γ)≠0 ∧
        ∀ x,(V.den γ).eval x=0 →
          (linear (C:L →+* L[X]) a (markJet S γ)).eval x≠0
def c5:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]} {F:Sheet Cq z S}
    (G:Generic F) (u:G.M),G.deriv u≠0→Nonempty (Projection G u)
def c6:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]} {F:Sheet Cq z S}
    (A:Pencil F) (γ:K) (hγ:γ∈F.marks),
    GraphCut (TY (A.pO γ) (seedResidue F γ hγ)
      (coords F.f A.x A.y)) A.a A.b →
    ∀ (u:A.bY γ),(u:A.M)=A.u →
      letI:=(eval₂RingHom (A.inChart γ) u).toAlgebra
      Module.Finite (seedRing F γ)[X] (A.bY γ)
private def toPencil (G:Generic F) (a b:Fin 4→L) (ha :G.form a≠0)
   (B:Projection G (G.form b/G.form a)) :Pencil F where
 M:=G.M
 field :=G.field
 aO8:=G.aO8
 overBase :=B.base
 tower :=B.tower
 finite :=B.finite
 separable :=B.separable
 x :=G.x
 y :=G.y
 independent:=G.independent
 equation :=(G.kernel F.f).mpr (dvd_refl _)
 generates :=G.generates
 polar_ne :=G.polar_ne
 y_ne :=G.y_ne
 a :=a
 b:=b
 gauge_ne :=ha
 value := by
   rw [B.parameter]
   exact (div_mul_cancel₀ _ ha).symm
private theorem linear_div {M:Type} [Field M] (j:L →+* M)
  (a :Fin 4→L) (v :Fin 4→M) (r :M) :
  linear j a (fun i=>v i/r)=linear j a v/r := by
 simp only [linear,div_eq_mul_inv,Finset.sum_mul,mul_assoc]
private theorem map_linear {R T:Type} [CommRing R] [CommRing T]
  (j:L →+* R) (f :R →+* T) (a :Fin 4→L) (v :Fin 4→R) :
  f (linear j a v)=linear (f.comp j) a (fun i=>f (v i)) := by
 simp only [linear,map_sum,map_mul,RingHom.comp_apply]
private def chartU (A:Pencil F) (γ:K) :A.bY γ :=
 linear (A.inChart γ |>.comp ((algebraMap L Cq.E).codRestrict (seedRing F γ) fun a=> by
  obtain rfl | h:=eq_or_ne a 0
  · simp
  · exact le_of_eq ((F.place γ).on_constants a h))) A.b (A.chartRatio γ)
private theorem chartU_val (A:Pencil F) (γ:K) : (chartU A γ:A.M)=A.u:= by
 let j:=(algebraMap Cq.E A.M).comp (algebraMap L Cq.E)
 change (A.bY γ).subtype (chartU A γ)=A.u
 rw [chartU,map_linear]
 change linear j A.b (fun i=>coords F.f A.x A.y i /
  linear j A.a (coords F.f A.x A.y))=A.u
 rw [linear_div]
 exact (div_eq_iff A.gauge_ne).mpr A.value
private theorem qR (G:Generic F) (a b:Fin 4→L) (ha :G.form a≠0)
   (P:Projection G (G.form b/G.form a))
   {γ:K} {hγ:γ∈F.marks} (T:MarkReduction G γ hγ)
   (hmark :linear (C:L →+* L[X]) a (markJet S γ)≠0) (B:L[X])
   (havoid : ∀ x,B.eval x=0→(linear (C:L →+* L[X]) a (markJet S γ)).eval x≠0)
   (hf :c6) (hcut:GraphCut (G.RS γ hγ) a b) :
   Nonempty (Chart (toPencil G a b ha P) γ hγ B) := by
 let A:=toPencil G a b ha P
 let k :L →+* seedRing F γ:=(algebraMap L Cq.E).codRestrict _ fun c=> by
   obtain rfl | hc:=eq_or_ne c 0
   · simp
   · exact le_of_eq ((F.place γ).on_constants c hc)
 let j:=T.seed.comp k
 have hj:T.O.subtype.comp j=G.constants :=RingHom.ext fun c=>T.seed_val (k c)
 have hr :T.red.comp j=phys.comp C:= by
   ext c
   change T.red (T.seed (k c))=phys (C c)
   rw [T.seed_red]
   congr 2
   change ((F.atPlace γ hγ) (algebraMap L Cq.E c)).coeff 0=c
   rw [AlgHom.commutes,LaurentSeries.algebraMap_apply]
   simp
 let d:=linear j a T.coord
 have hd: (d:G.M)=G.form a/evalXY F.f.derivative G.x G.y := by
   change T.O.subtype (linear j a T.coord)= _
   rw [map_linear,hj]
   rw [show (fun i=>T.O.subtype (T.coord i))=G.sW from funext T.coord_val]
   exact linear_div _ _ _ _
 have hred:T.red d=phys (linear (C:L →+* L[X]) a (markJet S γ)) := by
   change T.red (linear j a T.coord)= _
   rw [map_linear,hr,map_linear]
   simp_rw [T.coord_red]
 have hdred:T.red d≠0:= by
   rw [hred]
   simpa only [map_zero] using (show Function.Injective phys from IsFractionRing.injective L[X] _).ne hmark
 obtain ⟨e,he⟩:=(T.unit d hdred).exists_right_inv
 have hdiv {M:Type} [Field M] {m n k :M} (hk :k≠0) (hn:n≠0)
     (he' : (n/k)*m=1) (x :M) : (x/k)*m=x/n:= by
   calc
     _=(x/n)*((n/k)*m) := by field_simp
     _ = _:= by rw [he',mul_one]
 have heval : (G.form a/evalXY F.f.derivative G.x G.y)*(e :G.M)=1 := by
   have h:=congrArg T.O.subtype he
   simpa only [map_mul,map_one,Subring.subtype_apply,hd] using h
 have hx (i:Fin 4) : (T.coord i*e :T.O).val=A.ratio i:= by
   change (T.coord i:G.M)*(e :G.M)=G.point i/G.form a
   rw [T.coord_val]
   exact hdiv G.polar_ne ha heval _
 have hO:A.bY γ≤T.O:=Subring.closure_le.mpr (by
   rintro _ (⟨c,rfl⟩ | ⟨i,rfl⟩)
   · exact T.seed_val c ▸ (T.seed c).property
   · exact hx i ▸ (T.coord i*e).property)
 let ρ:=T.red.comp (Subring.inclusion hO)
 refine ⟨⟨chartU A γ,chartU_val A γ,hf A γ hγ hcut _ (chartU_val A γ),
   ρ,?_,hmark,?_,havoid⟩⟩
 · intro c
   have hc:Subring.inclusion hO (A.inChart γ c)=T.seed c :=
     Subtype.ext (T.seed_val c).symm
   exact (congrArg T.red hc).trans (T.seed_red c)
 · intro i
   have hi:Subring.inclusion hO (A.chartRatio γ i)=T.coord i*e :=Subtype.ext (hx i).symm
   have hρ: (T.red d)*T.red e=1 := by
     simpa only [map_mul,map_one] using congrArg T.red he
   change T.red (Subring.inclusion hO (A.chartRatio γ i)) =
     phys (markJet S γ i)/phys (linear (C:L →+* L[X]) a (markJet S γ))
   rw [hi,map_mul,T.coord_red,← hred]
   rw [eq_div_iff hdred,mul_assoc,mul_comm (T.red e) (T.red d),hρ,mul_one]
theorem of_children (ek :c1) (specialize :c2) (dim:c3)
  (cut:c4) (project :c5) (finite :c6) :qLXroAb.c4 := by
 intro q Cq z S F V hd hp
 obtain ⟨G⟩:=ek F hd hp
 obtain ⟨a,b,ha,hsep,hmarks⟩:=cut V G fun γ hγ=>dim G γ (V.Bp hγ)
 obtain ⟨P⟩:=project G _ hsep
 refine ⟨toPencil G a b ha P,fun γ hγ => ?_⟩
 obtain ⟨T⟩:=specialize V G γ hγ
 obtain ⟨hc,hm,hv⟩:=hmarks γ hγ
 exact qR G a b ha P T hm (V.den γ) hv finite hc
end
end q9uVqha
end
section
namespace qXARP7c
noncomputable section
open Polynomial WithZero
open scoped WithZero
open E7 (KB)
variable {D H J:Type} [Field D] [Field H] [Field J] [Algebra H J]
variable (v :Valuation H ℤᵐ⁰)
local notation "O" => v.valuationSubring
private theorem lift_poly {P:H[X]} (hP : ∀ i,v (P.coeff i)≤1) :
   ∃ Q:O[X],Q.map v.valuationSubring.subtype=P :=
 (lifts_iff_set_range P).mp ((lifts_iff_coeff_lifts P).mpr
   fun i=>⟨⟨P.coeff i,hP i⟩,rfl⟩)
private theorem scale_bound {P:H[X]} {s :H} (hs :v s=gauss v P) (hs0:s≠0) :
  ∀ i,v ((C s⁻¹*P).coeff i)≤1 := by
 intro i
 rw [coeff_C_mul,map_mul,map_inv₀,inv_mul_le_iff₀ (v.ne_zero_iff.mpr hs0 |> pos_iff_ne_zero.mpr),
  mul_one,hs]
 exact dMr v P i
private theorem unit_eval [Infinite D] (j:D →+* H) (hj : ∀ c,c≠0→v (j c)=1)
   {P:H[X]} (hP:P≠0) :
   ∃ c:D,c≠0∧v (P.eval (j c))=gauss v P:= by
 classical
 obtain ⟨i,hi,he⟩:=P.support.exists_mem_eq_sup (support_nonempty.mpr hP)
   (fun i=>v (P.coeff i))
 let s :=P.coeff i
 have hs0:s≠0:=mem_support_iff.mp hi
 obtain ⟨Q,hQ⟩:=lift_poly v (scale_bound v he.symm hs0)
 let l:D →+* O:=j.codRestrict v.valuationSubring.toSubring (fun x=> by
   by_cases hx :x=0
   · simp [hx]
   · exact (hj x hx).le)
 let r :=IsLocalRing.residue O
 have hQi:Q.coeff i=1 := by
   apply v.valuationSubring.subtype_injective
   rw [← coeff_map,hQ,coeff_C_mul,map_one]
   exact inv_mul_cancel₀ hs0
 have hQr :Q.map r≠0:= by
   intro h
   have h' := congrArg (fun T: (IsLocalRing.ResidueField O)[X]=>T.coeff i) h
   exact one_ne_zero (by simpa only [coeff_map,hQi,map_one,coeff_zero] using h')
 let bad:=(r.comp l) ⁻¹' {x | (Q.map r).IsRoot x}
 have hb:bad.Finite :=(finite_setOfPred_isRoot hQr).preimage (r.comp l).injective.injOn
 obtain ⟨c,hc⟩:=(hb.insert 0).exists_notMem
 have hc0:c≠0:= fun h=>hc (Or.inl h)
 have hcR:r (Q.eval (l c))≠0:= by
   intro h
   apply hc
   exact Or.inr (by simpa [bad,Polynomial.IsRoot,eval_map] using h)
 have hunit :v (v.valuationSubring.subtype (Q.eval (l c)))=1 := by
   apply le_antisymm (Q.eval (l c)).property
   exact le_of_not_gt fun h=>hcR ((IsLocalRing.residue_eq_zero_iff _).mpr
     (v.mem_maximalIdeal_iff.mpr h))
 have hvalue :v s⁻¹*v (P.eval (j c))=1 := by
   have hAt:=congrArg (fun W:H[X]=>W.eval (j c)) hQ
   rw [eval_map,eval_mul,eval_C] at hAt
   change Q.eval₂ v.valuationSubring.subtype (v.valuationSubring.subtype (l c))= _ at hAt
   rw [eval₂_at_apply] at hAt
   rw [← map_mul,← hAt]
   exact hunit
 refine ⟨c,hc0,?_⟩
 rw [map_inv₀,inv_mul_eq_iff_eq_mul₀ (v.ne_zero_iff.mpr hs0),mul_one] at hvalue
 exact hvalue.trans he.symm
private theorem val_norm_eval [Module.Finite H J] (a :J) (c:H) :
  (Algebra.lmul H J a).charpoly.eval c=Algebra.norm H (algebraMap H J c-a) := by
 rw [LinearMap.eval_charpoly,Algebra.norm_apply,map_sub (Algebra.lmul H J),(Algebra.lmul H J).commutes]
theorem eFi [Infinite D] [Module.Finite H J] (j:D →+* H)
    (hj : ∀ c,c≠0→v (j c)=1) (a :J) (ha :a≠0) :
    ∃ c:D,c≠0 ∧
      let b:=a/(algebraMap H J (j c)-a)
      b≠0∧IsIntegral O b ∧
      KB v (Algebra.norm H b)=j3 v (Algebra.lmul H J a).charpoly := by
  let P:=(Algebra.lmul H J a).charpoly
  obtain ⟨c,hc,he⟩:=unit_eval v j hj (P:=P) (LinearMap.charpoly_monic _).ne_zero
  let t:=j c
  let s :=P.eval t
  let d:=algebraMap H J t - a
  have hP:P≠0:=(LinearMap.charpoly_monic _).ne_zero
  have hs :s≠0:=v.ne_zero_iff.mp (he ▸ gauss_ne v hP)
  have hnorm:s=Algebra.norm H d:=val_norm_eval a t
  have hd:d≠0:=Algebra.norm_ne_zero_iff.mp (hnorm ▸ hs)
  obtain ⟨Q,hQ⟩:=lift_poly v (scale_bound v he hs)
  let t₀:O:=⟨t,(hj c hc).le⟩
  let T:= Q.comp (C t₀-Polynomial.X)
  have ht₀:T.coeff 0=1 := by
    apply v.valuationSubring.subtype_injective
    rw [← coeff_map,map_one,map_comp,hQ,Polynomial.map_sub,map_C,map_X,
      coeff_zero_eq_eval_zero,eval_comp]
    simp only [eval_sub,eval_C,eval_X,sub_zero,eval_mul]
    exact inv_mul_cancel₀ hs
  have hT:aeval d T=0:= by
    rw [aeval_comp,map_sub,aeval_C,aeval_X]
    have heq :algebraMap O J t₀ - d=a := by
      change algebraMap H J t - (algebraMap H J t - a)=a
      ring
    rw [heq,← aeval_map_algebraMap H]
    change aeval a (Q.map v.valuationSubring.subtype)=0
    rw [hQ,map_mul,aeval_C,Algebra.aeval_self_charpoly_lmul,mul_zero]
  have hinv :IsIntegral O d⁻¹:= by
    let:Invertible d:=invertibleOfNonzero hd
    refine ⟨T.reverse,?_,?_⟩
    · rwa [Monic,reverse_leadingCoeff,trailingCoeff_eq_coeff_zero (ht₀ ▸ one_ne_zero)]
    · simp only [← invOf_eq_inv]
      exact (eval₂_reverse_eq_zero_iff _ _ _).mpr hT
  have hb:IsIntegral O (a/d) := by
    rw [div_eq_mul_inv,show a*d⁻¹=algebraMap H J t*d⁻¹ - 1 by
      calc
        _=(algebraMap H J t - d)*d⁻¹:= by rw [show algebraMap H J t - d=a by simp [d]]
        _ = _:= by rw [sub_mul,mul_inv_cancel₀ hd]]
    exact ((isIntegral_algebraMap (x :=t₀)).mul hinv).sub isIntegral_one
  have hnorma :v (Algebra.norm H a)=v (P.coeff 0) := by
    rw [Algebra.norm_apply,LinearMap.det_eq_sign_charpoly_coeff]
    simp [P]
  have hcoeff :P.coeff 0≠0:= by
    intro h
    exact (v.ne_zero_iff.mpr (Algebra.norm_ne_zero_iff.mpr ha)) (by simp [hnorma,h])
  refine ⟨c,hc,div_ne_zero ha hd,hb,?_⟩
  change KB v (Algebra.norm H (a/d))=j3 v P
  rw [KB,div_eq_mul_inv,map_mul,Algebra.norm_inv,← div_eq_mul_inv,
    v.map_div,hnorma,← hnorm,he,j3,
    trailingCoeff_eq_coeff_zero hcoeff,log_div (v.ne_zero_iff.mpr hcoeff) (gauss_ne v hP),
    neg_sub]
theorem order_le_normalization (v :Valuation J ℤᵐ⁰) {a c:J} (ha :a≠0) (hc:v c=1) :
   KB v a≤KB v (a/(c-a)) := by
 by_cases h:v a<1
 · unfold KB
   rw [v.map_div,v.map_sub_eq_of_lt_left (hc ▸ h),hc,div_one]
 · have hlog:=(log_le_log one_ne_zero (v.ne_zero_iff.mpr ha)).2 (le_of_not_gt h)
   unfold KB
   rw [log_one] at hlog
   omega
end
end qXARP7c
end
