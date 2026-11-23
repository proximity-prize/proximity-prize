import ProximityPrize.SubmissionLower.ZWvyx4b
import ProximityPrize.SubmissionLower.ZMyjDge
import ProximityPrize.SubmissionLower.Zdhd3Ub
import ProximityPrize.SubmissionLower.Zgvu91a
import ProximityPrize.SubmissionLower.ZmXR7Cb
import ProximityPrize.SubmissionLower.Zc9uAjc
import ProximityPrize.SubmissionLower.ZNc0LBb
import ProximityPrize.SubmissionLower.ZEXP3Xa
import ProximityPrize.SubmissionLower.P6Split
import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZUURnQa
import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
open _root_ renaming Algebra.FiniteType → zUK, Algebra.IsAlgebraic → zjH, Function.Injective → zq4, IsFractionRing.injective → zxb, Polynomial.map_injective → zTo, Polynomial.trdeg_of_isDomain → zBA
section
section
namespace qWIOgVd
noncomputable section
open Polynomial Finset
open P5 (K)


open qGnV2ac (Sections zD atPair)
open q7kdBxd (Input)
theorem proof :q7kdBxd.c1 := by
  intro J S
  obtain ⟨a,ha⟩:=fresh S
  let D:=bY a
  obtain ⟨R⟩:=rechart J D
  let G:Input :=⟨R.F,J.l,J.h,J.s,J.b,R.Ca,R.weight⟩
  let j (γ:K) :=width J.s (S.P γ) (S.Q γ)
  let t (γ:K) :=J.s+2*j γ
  let d (γ:K) :=width (t γ) (S.A γ) (S.B γ)
  let P' (γ:K) :=rev a (j γ+J.s) (S.P γ)
  let Q' (γ:K) :=rev a (j γ) (S.Q γ)
  let A' (γ:K) :=rev a (d γ+t γ) (S.A γ)
  let B' (γ:K) :=rev a (d γ) (S.B γ)
  have hq (γ:K) (hγ:γ∈S.CF) :=S.denominator γ hγ
  have hpq (γ:K) :=at_pair R (S.seed γ) (S.P γ) (S.Q γ) (P' γ) (Q' γ) (rev_ratio D J.s)
  have hsimple (γ:K) (hγ:γ∈S.CF) :
      D.changeX (atPair J.F.derivative (S.seed γ) (S.P γ) (S.Q γ))≠0 :=
    fun h=>S.simple γ hγ (D.changeX.injective (h.trans (map_zero D.changeX).symm))
  have hx (γ:K) (hγ:γ∈S.CF) :
      zD R.F (S.seed γ) (P' γ) (Q' γ) =
        x^(t γ)*D.changeX (zD J.F (S.seed γ) (S.P γ) (S.Q γ)) := by
    obtain ⟨_,hy,hz⟩:=hpq γ
    unfold zD
    rw [hy,hz,show Q' γ=rev a (j γ) (S.Q γ) from rfl,
      D.CJ _ _ (width_bound J.s (S.P γ) (S.Q γ)).2]
    simp only [map_mul,map_neg,map_div₀,map_pow,t,pow_add,pow_mul]
    field_simp [R.scalar_ne,x_ne,hsimple γ hγ]
    ring
  let T:Sections G.F := {
    CF:=S.CF
    seed :=S.seed
    injective :=S.injective
    P:=P'
    Q:= Q'
    denominator := fun γ hγ=>rev_ne a _ (hq γ hγ)
    coprime := fun γ hγ=>rev_coprime a J.s (hq γ hγ) (S.coprime γ hγ)
    root := fun γ hγ=> by rw [show G.F=R.F from rfl,(hpq γ).1,S.root γ hγ,map_zero,mul_zero]
    regular_ordinate := fun γ hγ=>regular_ordinate R (S.seed γ) (S.regular_ordinate γ hγ)
    simple := fun γ hγ=> by
      rw [show G.F=R.F from rfl,(hpq γ).2.1]
      exact mul_ne_zero (mul_ne_zero R.scalar_ne (inv_ne_zero (pow_ne_zero _ x_ne)))
        (hsimple γ hγ)
    A:=A'
    B:=B'
    nonzero := fun γ hγ=>rev_ne a _ (S.nonzero γ hγ)
    pole_denominator := fun γ hγ=>rev_ne a _ (S.pole_denominator γ hγ)
    reduced:= fun γ hγ=>rev_coprime a (t γ) (S.pole_denominator γ hγ) (S.reduced γ hγ)
    formula := fun γ hγ=> by
      rw [rev_ratio D (t γ),S.formula γ hγ,← hx γ hγ] }
  refine ⟨G,T,rfl,rfl,rfl,rfl,le_of_eq ?_⟩
  apply sum_congr rfl
  intro γ hγ
  change d γ=(rev a (d γ) (S.B γ)).natDegree
  exact (rev_degree (width_bound (t γ) (S.A γ) (S.B γ)).2 (ha γ hγ)).symm
end
end qWIOgVd
end
section
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 12
set_option synthInstance.maxSize 512
namespace q6lciJe
noncomputable section
open Polynomial
open cu (L)
open qrKC9pb qyUzJvd
open scoped WithZero nonZeroDivisors
open private localValuation from ProximityPrize.SubmissionLower.ZDlyzqd
open private finiteTypeClosedHeight from ProximityPrize.SubmissionLower.Zf9vSCd
private theorem evalSeed_injective (J:Input) (r :Bool) :
  zq4 (evalSeed J r) := by
 apply Function.Injective.of_comp (f :=algebraMap (Chart J r) (EC J))
 change zq4 ((algebraMap (Chart J r) (EC J)).comp (evalSeed J r))
 rw [coe_evalSeed J r]
 apply (injective_iff_map_eq_zero _).mpr
 intro a ha
 by_contra hn
 exact rootMap_ne_zero_of_degree J (C_ne_zero.mpr hn) (by
  rw [natDegree_C]
  exact (by decide :0<2).trans_le J.Ca.two_le) ha
private theorem normalFraction (J:Input) (r :Bool) :
   IsFractionRing (Normal J r) (EC J) := by
 let B:=Polynomial (Polynomial L)
 let A:Type :=Chart J r
 let S:=AdjoinRoot J.F
 let F:=EC J
 have :zjH B S:= by
   have h:=Algebra.isAlgebraic_adjoin_singleton_iff.mpr
     (AdjoinRoot.isAlgebraic_root J.Ca.irreducible.ne_zero)
   rw [AdjoinRoot.adjoinRoot_eq_top] at h
   exact ⟨fun a=>h a (by trivial)⟩
 have :zjH S F:=IsLocalization.isAlgebraic F (nonZeroDivisors S)
 have :zjH B F:=Algebra.IsAlgebraic.trans B S F
 let:Algebra B A:=(evalSeed J r).toAlgebra
 have :IsScalarTower B A F:= by
   apply IsScalarTower.of_algebraMap_eq'
   change (a7W J).comp C=(algebraMap (Chart J r) (EC J)).comp (evalSeed J r)
   exact (coe_evalSeed J r).symm
 have :zjH A F:=Algebra.IsAlgebraic.extendScalars (evalSeed_injective J r)
 exact integralClosure.isFractionRing_of_algebraic (A:=A) (L:=F)
   fun _ h=>Subtype.val_injective h
private theorem chartTrdeg (J:Input) (r :Bool) :2≤Algebra.trdeg L (Chart J r) := by
  let f :L[X][X] →ₐ[L] Chart J r :=
    { evalSeed J r with
      commutes' := fun c=> by
        apply Subtype.val_injective
        change ((algebraMap (Chart J r) (EC J)).comp (evalSeed J r)) (C (C c)) =
          algebraMap L (EC J) c
        rw [coe_evalSeed J r]
        rfl }
  have :FaithfulSMul L[X] (L[X][X]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Polynomial.C_injective
  have hdim:Algebra.trdeg L (L[X][X])=2 := by
    rw [← trdeg_add_eq L L[X] (A:=L[X][X]),zBA,
      zBA,one_add_one_eq_two]
  rw [← hdim]
  exact trdeg_le_of_injective f (evalSeed_injective J r)
private theorem maximal_of_coord (J:Input) (r :Bool) (q:Ideal (Chart J r)) [q.IsPrime]
    (h : ∀ i,∃ c:L,coord J r i-algebraMap L (Chart J r) c∈q) :q.IsMaximal:= by
  let A:Type :=Chart J r
  let f :=Ideal.Quotient.mkₐ L q
  have hs :Function.Surjective (algebraMap L (A ⧸ q)) := by
    intro z
    obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective z
    change ∃ c,algebraMap L (A ⧸ q) c=f a
    obtain ⟨a,ha⟩:=a
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i,rfl⟩:=ha
      obtain ⟨c,hc⟩:=h i
      exact ⟨c,(f.commutes c).symm.trans
        (Ideal.Quotient.eq.mpr hc).symm⟩
    | algebraMap a=>exact ⟨a,(f.commutes a).symm⟩
    | add a b hx hy ha hb =>
      obtain ⟨a',ha⟩:=ha
      obtain ⟨b',hb⟩:=hb
      refine ⟨a' + b',?_⟩
      rw [(algebraMap L (A ⧸ q)).map_add,ha,hb]
      exact (map_add f ⟨a,hx⟩ ⟨b,hy⟩).symm
    | mul a b hx hy ha hb =>
      obtain ⟨a',ha⟩:=ha
      obtain ⟨b',hb⟩:=hb
      refine ⟨a' * b',?_⟩
      rw [(algebraMap L (A ⧸ q)).map_mul,ha,hb]
      exact (map_mul f ⟨a,hx⟩ ⟨b,hy⟩).symm
  have :Nontrivial (A ⧸ q) :=Ideal.Quotient.nontrivial_iff.mpr ‹q.IsPrime›.ne_top
  let e :=RingEquiv.ofBijective (algebraMap L (A ⧸ q)) ⟨(algebraMap L _).injective,hs⟩
  exact Ideal.Quotient.maximal_of_isField q (e.symm.toMulEquiv.isField (Field.toIsField L))
theorem proof :qyUzJvd.c3:= by
 classical
 intro J r hf P hP hheight
 let A:Type :=Chart J r
 let N :=Normal J r
 let F:=EC J
 have :Module.Finite A N :=hf
 have :zUK L A :=
   Algebra.FiniteType.adjoin_of_finite (Set.finite_range (aD J r))
 have :zUK L N :=
   Algebra.FiniteType.trans (inferInstance :zUK L A)
     (inferInstance :zUK A N)
 have :IsNoetherianRing N :=Algebra.FiniteType.isNoetherianRing L N
 have :IsFractionRing N F:=normalFraction J r
 have :IsIntegrallyClosed N :=(isIntegrallyClosed_iff_isIntegrallyClosedIn (R:=N) F).mpr inferInstance
 obtain ⟨v,hv,hcenter,hreg,hu⟩:=localValuation (K:=F) P hheight
 have hchart (a :A) :v (a :F)<1↔algebraMap A N a∈P:=hcenter (algebraMap A N a)
 have hc (c:L) (h:c≠0) :v (constant J c)=1 := by
   let b:=algebraMap A N (algebraMap L A c)
   change v (algebraMap N F b)=1
   refine (hreg b).antisymm (le_of_not_gt fun hlt=>hP.ne_top ?_)
   exact P.eq_top_of_isUnit_mem ((hcenter b).mp hlt)
     (((isUnit_iff_ne_zero.mpr h).map (algebraMap L A)).map (algebraMap A N))
 have hcurve : ∃ i,¬ ResidueConstant J v (aD J r i) := by
   by_contra! h
   let q:=P.under A
   have :q.IsPrime :=Ideal.IsPrime.under A P
   have hq:q.IsMaximal:=maximal_of_coord J r q fun i=> by
     obtain ⟨c,hc⟩:=h i
     exact ⟨c,(hchart (coord J r i-algebraMap L A c)).mp hc⟩
   have :P.IsMaximal:=Ideal.isMaximal_of_isIntegral_of_isMaximal_under P hq
   let f :A →ₐ[L] N :=IsScalarTower.toAlgHom L A N
   have hfi:zq4 f := fun _ _ h =>
     Subtype.ext (congrArg (fun a :N=>(a :F)) h)
   have hh:=finiteTypeClosedHeight ((chartTrdeg J r).trans (trdeg_le_of_injective f hfi)) P
   rw [hheight] at hh
   exact (by decide : ¬ (2 :ℕ∞)≤1) hh
 exact ⟨⟨v,hv,hc,fun i=>hreg (algebraMap A N (coord J r i)),hcurve⟩,hchart,hu⟩
end
end q6lciJe
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace qwGrtCa
noncomputable section
open Polynomial Finset
open scoped nonZeroDivisors Classical
open P5 (K)
open P5_7 (OneSeedEquation atNative)
open cu (L FX kr jz)
open P5_7_7 (Dg DualWord embed phys mL sites gY bv9 nativeEval dualValue)
open qyWKMud (changed linear)
private theorem phys_inj:zq4 phys :=zxb L[X] FX
private theorem phys_ne {b:L[X]} (hb:b≠0) :phys b≠0 :=
 (map_ne_zero_iff phys phys_inj).mpr hb
private theorem embed_degree (F:Dg) : (embed F).natDegree=F.natDegree :=
 natDegree_map_eq_of_injective (zTo _ phys_inj) F
private theorem embed_coeff_degree (F:Dg) (i:ℕ) :
  ((embed F).coeff i).natDegree=(F.coeff i).natDegree := by
 simp only [embed,coe_mapRingHom,coeff_map,
  natDegree_map_eq_of_injective (zxb L[X] FX)]
private theorem scale_unit {a :FX} (ha :a≠0) :IsUnit (C (C a) :OneSeedEquation) :=
 ((isUnit_iff_ne_zero.mpr ha).map C).map C
private theorem scale_height {a :FX} (ha :a≠0) (f :OneSeedEquation) :
  gY (C (C a)*f)=gY f := by
 unfold gY
 rw [map_mul,Bivariate.swap_C_C,natDegree_C_mul (C_ne_zero.mpr ha)]
private theorem clear_phys (f :OneSeedEquation) :
  ∃ (Q:Dg) (a :FX),a≠0∧embed Q=C (C a)*f := by
 let:Algebra (L[X][X]) (FX[X]) :=Polynomial.algebra (L[X]) FX
 let M:=(L[X])⁰.map (C:L[X] →+* L[X][X])
 let:IsLocalization M FX[X] :=Polynomial.isLocalization (L[X])⁰ FX
 let Q:Dg:=IsLocalization.integerNormalization M f
 obtain ⟨_,⟨a,ha,rfl⟩,hQ⟩:=IsLocalization.integerNormalization_spec M f
 rw [Algebra.smul_def (C a :L[X][X]) f] at hQ
 change embed Q=C ((C a).map (algebraMap L[X] FX))*f at hQ
 rw [map_C] at hQ
 exact ⟨Q,phys a,phys_ne (nonZeroDivisors.ne_zero ha),hQ⟩
private theorem ccE (g:OneSeedEquation) (hi:Irreducible g)
   (hd:g.natDegree≠0) : ∃ (F:Dg) (s :FX),s≠0 ∧
     embed F=C (C s)*g∧Irreducible F∧Irreducible (embed F) := by
 obtain ⟨Q,a,ha,hQ⟩:=clear_phys g
 have hiQ:Irreducible (embed Q) :=hQ ▸ (irreducible_isUnit_mul (scale_unit ha)).mpr hi
 have hdQ: (embed Q).natDegree≠0:= by
   rwa [hQ,natDegree_C_mul (C_ne_zero.mpr ha)]
 let:NormalizedGCDMonoid L[X][X] :=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
 let c:= Q.content
 let F:= Q.primPart
 have hfact :embed Q=C (c.map phys)*embed F:= by
   have he :=congrArg embed Q.eq_C_content_mul_primPart
   simpa only [map_mul,embed,phys,c,F,coe_mapRingHom,map_C] using he
 have hunit :=(hiQ.isPrimitive hdQ) (c.map phys) ⟨embed F,hfact⟩
 have hc:c=C (c.coeff 0) :=eq_C_of_natDegree_eq_zero (by
   rw [← natDegree_map_eq_of_injective phys_inj c]
   exact natDegree_eq_zero_of_isUnit hunit)
 let b:=phys (c.coeff 0)
 have hcb:c.map phys=C b:= by conv_lhs=>rw [hc,map_C]
 have hb:b≠0:= fun hz=>hunit.ne_zero (by rw [hcb,hz,C_0])
 have hr :C (C b)*embed F=C (C a)*g:=hcb ▸ hfact.symm.trans hQ
 have hF:embed F=C (C (b⁻¹*a))*g:= calc
   embed F=C (C b⁻¹)*(C (C b)*embed F) := by
     rw [← mul_assoc,← map_mul,← map_mul,inv_mul_cancel₀ hb,map_one,map_one,one_mul]
   _=C (C (b⁻¹*a))*g:= by rw [hr,map_mul,map_mul,mul_assoc]
 have hs :b⁻¹*a≠0:=mul_ne_zero (inv_ne_zero hb) ha
 have hiF:Irreducible (embed F) :=hF ▸ (irreducible_isUnit_mul (scale_unit hs)).mpr hi
 exact ⟨F,_,hs,hF,
   Q.isPrimitive_primPart.irreducible_of_irreducible_map_of_injective
     (zTo _ phys_inj) hiF,hiF⟩
private theorem height_le (a b c d:FX) (n:ℕ) (f :OneSeedEquation) :
   gY (transform (C a) (C b) (C c) (C d) n f)≤gY f := by
 have hf (v w:FX) :Bivariate.swap (form (C v) (C w)) =
     C (C w+C v*Polynomial.X (R:=FX)) := by
   simp only [form,map_add,map_mul,Bivariate.swap_C_C,Bivariate.swap_Y]
 unfold gY
 rw [transform_sum,map_sum]
 refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
 rw [map_mul,map_mul,map_pow,map_pow,hf,hf,Bivariate.swap_C,← map_pow,← map_pow]
 refine (natDegree_mul_C_le _ _).trans ((natDegree_mul_C_le _ _).trans ?_)
 rw [natDegree_map_eq_of_injective C_injective]
 exact (bv9 f _).mp le_rfl i
private theorem chart_data {D w U S} (J:DualWord D w U S) (f :OneSeedEquation)
   (hi:Irreducible f) (hn:2≤f.natDegree) :
   Irreducible (changed J f)∧(changed J f).natDegree=f.natDegree ∧
     gY (changed J f)=gY f := by
 let a :=phys J.b₀
 let b := -phys J.b₁
 let c := -phys J.a₀
 let d:=phys J.a₁
 obtain ⟨q,hq,hJ⟩:=J.determinant
 have hd:=phys_ne (show J.a₀*J.b₁-J.a₁*J.b₀≠0 by
   rw [hJ]; exact mul_ne_zero (C_ne_zero.mpr hq) (q20JTGa.locator_ne univ))
 have hdet:a*d-b*c = -phys (J.a₀*J.b₁-J.a₁*J.b₀) := by
   simp only [a,b,c,d,map_sub,map_mul]
   ring
 let u:=(a*d-b*c)⁻¹
 have hu:u*(a*d-b*c)=1 :=inv_mul_cancel₀ (hdet ▸ neg_ne_zero.mpr hd)
 have hu' : (C u:FX[X])*(C a*C d-C b*C c)=1 := by
   simpa only [map_mul,map_sub,map_one] using congrArg (C:FX →+* FX[X]) hu
 have he :changed J f=transform (C a) (C b) (C c) (C d) f.natDegree f := by
   rw [changed,transform_sum]
   simp only [linear,form,a,b,c,d,map_neg]
 rw [he]
 obtain ⟨hg,hdg⟩:=transform_irred _ _ _ _ _ hu' hi hn
 refine ⟨hg,hdg,le_antisymm (height_le a b c d _ f) ?_⟩
 have hh:=height_le (u*d) (-(u*b)) (-(u*c)) (u*a) f.natDegree
   (transform (C a) (C b) (C c) (C d) f.natDegree f)
 simp only [map_mul,map_neg] at hh
 rwa [transform_inverse _ _ _ _ _ hu' le_rfl] at hh
private theorem chart_root {D w U S} (J:DualWord D w U S) (f :OneSeedEquation)
   {γ:K} (hγ:γ∈U) (z :K) (hr :atNative f z (S γ)=0) :
   nativeEval z (dualValue J γ) (changed J f)=0:= by
 let v :=dualValue J γ
 let s :=kr (S γ)
 let N :=phys J.b₀*v - phys J.b₁
 let B:=phys J.a₁ - phys J.a₀*v
 let ev :=nativeEval z v
 have hnum :phys (mL (sites w S γ))*phys (J.P γ)=phys J.a₁*s+phys J.b₁:= by
   simpa only [s,kr,phys,map_add,map_mul] using congrArg phys (J.numerator_id γ hγ)
 have hden:phys (mL (sites w S γ))*phys (J.Q γ)=phys J.a₀*s+phys J.b₀:= by
   simpa only [s,kr,phys,map_add,map_mul] using congrArg phys (J.denominator_id γ hγ)
 have hratio: (phys J.a₀*s+phys J.b₀)*v=phys J.a₁*s+phys J.b₁:= by
   rw [← hden,← hnum,mul_assoc]
   have h:=mul_div_cancel₀ (phys (J.P γ)) (phys_ne (J.denominator γ hγ))
   exact congrArg (phys (mL (sites w S γ)) * ·) h
 have hNB:N=s*B:= by dsimp only [N,B]; linear_combination hratio
 have evC (q:FX[X]) :ev (C q)=q.eval (jz z) := by simp [ev,nativeEval]
 have evLin (a b:L[X]) :ev (linear a b)=phys a+phys b*v := by
   simp [linear,map_add,map_mul,ev,nativeEval]
 have evN :ev (linear (-J.b₁) J.b₀)=N := by rw [evLin,map_neg,add_comm,← sub_eq_add_neg]
 have evB:ev (linear J.a₁ (-J.a₀))=B:= by rw [evLin,map_neg,neg_mul,← sub_eq_add_neg]
 have he :ev (changed J f)=atNative f z (S γ)*B^f.natDegree := by
   rw [changed,map_sum,atNative,eval₂_eq_sum_range,sum_mul]
   apply sum_congr rfl
   intro i hi
   have hp:i+(f.natDegree-i)=f.natDegree :=
     Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hi))
   simp only [map_mul,map_pow,evN,evB,evC,hNB,mul_pow,coe_evalRingHom]
   rw [mul_assoc _ (_ *_),mul_assoc (_^i),← pow_add,hp,← mul_assoc]
 exact he.trans (by rw [hr,zero_mul])
theorem proof :qyWKMud.c1 := by
 intro D w U S J f hf hn T z hT hr
 obtain ⟨hg,hd,hh⟩:=chart_data J f hf hn
 obtain ⟨F,a,ha,repr,hi,hi'⟩:=ccE _ hg (by rw [hd]; omega)
 have hheight:gY (embed F)=gY f := by rw [repr,scale_height ha,hh]
 refine ⟨⟨F,hi,hi',⟨a,ha,repr⟩,?_,hheight,?_⟩,?_⟩
 · rw [← embed_degree,repr,natDegree_C_mul (C_ne_zero.mpr ha),hd]
 · intro i
   rw [← embed_coeff_degree,← hheight]
   exact (bv9 _ _).mp le_rfl i
 · intro γ hγ
   change nativeEval (z γ) (dualValue J γ) (embed F)=0
   rw [repr,map_mul,chart_root J f (hT hγ) (z γ) (hr γ hγ),mul_zero]
end
end qwGrtCa
end
end
section
set_option autoImplicit true
namespace P6_7
noncomputable section
open Polynomial
open P6 (p)
open P5_7 (InFar Test Lc terminal agA O2 farAgreement aRe ctc far_guards ahs bAN)
open cu (vP Jet Equation)
open qQ (zI N5 aLQ wU)
private theorem eHv {b H u del} {M:P1.FJ H u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:InFar b M.iF)
    (x :Test b) {q:zI} (hq:N5 q) (hv :agA rows (terminal b).shape q)
    {W} (hW:W<(Lc b x).shape.m*farAgreement) {P:Jet}
    (hP:P∈rows (Lc b x).shape W) :
    wU q P (ahs M.iF.toNat (Lc b x).shape W) := by
  let h:=M.iF.toNat
  let t:=Lc b x
  obtain ⟨ht,hm,hb,hj,hu⟩:=ctc b x
  have hchar :t.shape.m*farAgreement<p:=hm ▸ (far_guards b).2.2.2.1
  apply baD.proof _ _ _ hq
  · have hd:=Nat.div_le_self (O2 t.shape-W) (2*h)
    change 1+(O2 t.shape-W)/(2*h)<p
    change W<t.shape.m*farAgreement at hW
    unfold O2 at *
    omega
  intro a c hac
  change a+c<1+(O2 t.shape-W)/(2*h) at hac
  have hh:0<h:=(far_guards b).1.trans_le (aRe hw).1
  have hc:=(Nat.le_div_iff_mul_le (by omega :0<2*h)).mp
    (show a+c≤(O2 t.shape-W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c),Nat.mul_add] at hc
  have top:O2 t.shape=O2 (terminal b).shape :=
    congrArg (fun m=>m*farAgreement - 1) hm
  have hwc:W≤O2 t.shape := by
    change W<t.shape.m*farAgreement at hW
    unfold O2
    omega
  have hw' : W+2*h*a+2*h*c≤O2 (terminal b).shape := by omega
  have ha :=src.shift t ht W P hP 0 a
  have hc' := src.shift t ht _ _ ha 1 c
  exact hv _ (src.nested t ht _ (Or.inl rfl) hm hb hj hu _ _ hw' hc')
theorem gDx {b H u del} {M:P1.FJ H u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:InFar b M.iF)
    {qs :Finset zI} (hq : ∀ q∈qs,N5 q)
    (hp : ∀ q∈qs,agA rows (terminal b).shape q) {f :Equation}
    (hf :aLQ qs f) (x :Test b) :
    bAN M.iF.toNat (Lc b x) rows f := by
  have ht:=(ctc b x).1
  refine ⟨src.ajB _ ht,src.shape _ ht,src.leading _ ht,?_⟩
  intro W hW P hP hn
  exact hf.divides_leading P _ hn
    (fun q h=>eHv src hw x (hq q h) (hp q h) hW hP)
end
end P6_7
end
section
set_option autoImplicit true
namespace P6_7
open P6 (gJ)
open P5_7 (FarBand InFar Qn HeightPrice lateRows)
private inductive Cover (cap hi:ℕ) :ℕ→List HeightPrice→Prop where
  | nil {lo} : lo=hi+1→ Cover cap hi lo []
  | cons {lo r rs} : r.lo=lo→ r.lo≤ r.hi→ r.cap≤ cap→ Cover cap hi (r.hi+1) rs →
      Cover cap hi lo (r :: rs)
private theorem covered {cap hi lo xs} (checked :Cover cap hi lo xs) {w:ℤ}
    (hl: (lo:ℤ)≤w) (hh:w≤(hi:ℤ)) :
    ∃ r∈xs,Qn r.lo r.hi w∧r.cap≤ cap:= by
  induction checked with
  | nil=>omega
  | @cons lo r rs heq _ hc _ ih =>
    by_cases hw:w≤(r.hi:ℤ)
    · exact ⟨r,List.mem_cons_self,⟨by simpa only [heq] using hl,hw⟩,hc⟩
    · obtain ⟨r',hr',hb,hp⟩:=ih (by omega)
      exact ⟨r',List.mem_cons_of_mem _ hr',hb,hp⟩
private theorem near_checked :Cover gJ.near.regular 2703 2535 nearRows := by
  unfold nearRows P5_7.nearRows
  simp only [List.drop_succ_cons,List.drop_zero]
  repeat' first | exact Cover.nil rfl | (apply Cover.cons <;> try decide)
theorem near_coverage {w:ℤ} (hl:2535≤w) (hh:w≤2703) :
    ∃ r∈nearRows,Qn r.lo r.hi w∧r.cap≤gJ.near.regular :=
  covered near_checked hl hh
private theorem late_checked :Cover gJ.middle.regular 3599 2704 lateRows := by
  unfold P5_7.lateRows
  repeat' first | exact Cover.nil rfl | (apply Cover.cons <;> try decide)
theorem late_coverage {w:ℤ} (hl:2704≤w) (hh:w≤3599) :
    ∃ r∈lateRows,Qn r.lo r.hi w∧r.cap≤gJ.middle.regular :=
  covered late_checked hl hh
theorem far_coverage {w:ℤ} (hl:3600≤w) (hh:w≤33561) :
    ∃ b:FarBand,InFar b w:= by
  by_cases hw:w≤33463
  · exact P5_7.far_coverage hl hw
  · exact ⟨.wQ,show (32411 :ℤ)≤w∧w≤33657 from by omega⟩
end P6_7
end
section
set_option autoImplicit true
namespace P6_7
noncomputable section
open Polynomial
open P6 (gJ jG K dw)
open P5_7 (FarBand InFar farAgreement midAgreement Pairs lateRows Lc ctc aRe far_guards eiO grade_seed grade_guard grade_paid eqx native_restriction wX cV)
open cu (vP yq)
def c1 :Prop :=RegularBound dw (jX .rectTight)
def c2 :Prop := ∀ b:RectTail,RegularBound dw (jX b.kA)
def c3:Prop :=RegularBound dw (jX .graph)
def c4 :Prop := ∀ r∈nearRows,RegularBound midAgreement r
def c5:Prop := ∀ r∈lateRows,RegularBound midAgreement r
def c6:Prop :=
  ∀ (b:FarBand) u del (M:jG u del) Γ (F:P1.bje farAgreement M Γ),
    InFar b M.iF→M.shift∉Γ → ∀ H,YQ M F H →
    ∃ rows :vP,Source b M F rows∧Nonempty (Pairs b M.iF.toNat rows)
def c7:Prop :=
  ∀ (b:FarBand) u del (M:jG u del) Γ (F:P1.bje farAgreement M Γ),
    InFar b M.iF→M.shift∉Γ → ∀ H,YQ M F H →
    ∀ rows,Source b M F rows → ∀ pairs :Pairs b M.iF.toNat rows,
    Nonempty (bkU b M F pairs)
def c8:Prop :=qyWKMud.c2∧qGnV2ac.c1∧qGnV2ac.c2
private theorem native_count (h8:c8) :P5_7.c7 :=
  qyWKMud.of_children q1tes5a.proof q20JTGa.proof qwGrtCa.proof
    h8.1 h8.2.1 h8.2.2
private theorem far_count (h6:c6) (h7:c7) (native :P5_7.c7)
    {b u del} (M:jG u del) (Γ:Finset K) (F:P1.bje farAgreement M Γ)
    (hw:InFar b M.iF) (hshift:M.shift∉Γ)
    (H) (hH :YQ M F H) :Γ.card≤gJ.far.regular := by
  classical
  obtain ⟨rows,src,⟨pairs⟩⟩:=h6 b u del M Γ F hw hshift H hH
  obtain ⟨Q⟩:=h7 b u del M Γ F hw hshift H hH rows src pairs
  let T:=Γ \ Q.book
  have hT:T⊆Γ:=Finset.sdiff_subset
  have hprefix : (Γ \ T).card≤b.row.prefixFee := by
    apply (Finset.card_le_card ?_).trans Q.book_bound
    intro γ hγ
    obtain ⟨ha,hn⟩:=Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have hpart:=Finset.card_sdiff_add_card_eq_card hT
  have cover : ∀ γ∈T,∃ q∈Q.parents,axy M F q γ:= fun γ hγ =>
    (Q.Eh γ (hT hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  by_cases hm:T.Nonempty
  · obtain ⟨γ,hγ⟩:=hm
    obtain ⟨q,hq,_⟩:=cover γ hγ
    obtain ⟨f,hf⟩:=czI.proof Q.parents ⟨q,hq⟩ Q.geometric
    have hne :f≠0:= by
      intro hz
      have h:=hf.positive
      simp only [hz,natDegree_zero,lt_self_iff_false] at h
    obtain ⟨hl,hu⟩:=aRe hw
    obtain ⟨hlo,hhi,htop,_,hwidth,_⟩:=far_guards b
    obtain ⟨i,he,hs⟩:=eiO (b:=b) hf.positive (by
      intro x hE hv
      have trace :=gDx src hw Q.geometric Q.terminal_pass hf x
      obtain ⟨_,ht,hb,_,_⟩:=ctc b x
      have hwidth' : (Lc b x).shape.B*(131071-M.iF.toNat) ≤
          (Lc b x).shape.m*farAgreement:= by
        rw [ht,hb]
        exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
      exact (P5_7_6.proof b _ hl hu x).not_ge
        (eqx (by omega) (by omega) x hne trace (ht ▸ htop) hwidth' hE hv))
    obtain ⟨g,hg,hge,hgs,hgraph⟩:=native_restriction hne (grade_seed b i) hs
    have hkept:=native (wX b) (i.val+1) _ (cV b i).rate (grade_guard b i)
      M.word T M.label F.scalar (fun _ _ _ _ h=>sub_left_inj.mp h) (F.distinct.mono hT)
      (fun γ hγ=>(aic F (hT hγ)).trans (Nat.add_le_add_left hu _))
      (fun γ hγ =>
        let m:=F.mark γ (hT hγ)
        ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩)
      g hg (hge.trans he.le) hgs (fun γ hγ=> by
        rw [hgraph]
        obtain ⟨q',hq',hon⟩:=cover γ hγ
        have hz :=RingHom.mem_ker.mp (hon (hf.aiq q' hq'))
        simpa only [coe_eval₂RingHom,eval₂_C,yq] using hz)
    exact (hpart ▸ Nat.add_le_add hprefix hkept).trans (grade_paid b i)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hm,Finset.sdiff_empty] at hprefix
    exact hprefix.trans (far_guards b).2.2.2.2.2
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
    (h6:c6) (h7:c7) (h8:c8) :P6.c7:= by
  intro b u del M Γ F hshift hlo hhi
  obtain ⟨H,hH⟩:=dsh M F
  cases b with
  | rectTight=>exact h1 u del M Γ F ⟨hlo,hhi⟩ hshift H hH
  | rectPruned=>exact h2 .pruned u del M Γ F ⟨hlo,hhi⟩ hshift H hH
  | rectTailOne=>exact h2 .tailOne u del M Γ F ⟨hlo,hhi⟩ hshift H hH
  | rectTailTwo=>exact h2 .tailTwo u del M Γ F ⟨hlo,hhi⟩ hshift H hH
  | rectTailThree=>exact h2 .tailThree u del M Γ F ⟨hlo,hhi⟩ hshift H hH
  | graph=>exact h3 u del M Γ F ⟨hlo,hhi⟩ hshift H hH
  | near =>
    let G:P1.bje midAgreement M Γ:=weakenFamily F (by decide)
    obtain ⟨r,hr,hw,hc⟩:=near_coverage hlo hhi
    exact (h4 r hr u del M Γ G hw hshift H hH).trans hc
  | middle =>
    let G:P1.bje midAgreement M Γ:=weakenFamily F (by decide)
    obtain ⟨r,hr,hw,hc⟩:=late_coverage hlo hhi
    exact (h5 r hr u del M Γ G hw hshift H hH).trans hc
  | far =>
    let G:P1.bje farAgreement M Γ:=weakenFamily F (by decide)
    obtain ⟨q,hw⟩:=far_coverage hlo hhi
    exact far_count h6 h7 (native_count h8) M Γ G hw hshift H hH
end
end P6_7
end
section
set_option autoImplicit true
namespace qXdgDRd
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K I p blockLength)
open P5_7 (NativeWitness farAgreement)
open P5_7_7
open qGnV2ac
open cu (L)
abbrev gap (D:ℕ) :=P6.dw-D
abbrev width (D:ℕ) :=blockLength+D-2*P6.dw
abbrev shift:=P6.dw-farAgreement
structure StrongMarks (D:ℕ) (w:I→K) (T:Finset K) (z :K→K)
    (S:K→K[X]) :Prop extends UJ D w T z S where
  strong : ∀ γ∈T,P6.dw≤(sites w S γ).card
theorem StrongMarks.restrict {D w T z S} (M:StrongMarks D w T z S)
    {U:Finset K} (hU:U⊆T) :StrongMarks D w U z S :=
  ⟨⟨M.Kw.mono hU,M.sections.mono hU,fun γ h=>M.degree γ (hU h),
    fun γ h=>M.dw γ (hU h)⟩,fun γ h=>M.strong γ (hU h)⟩
theorem chart_bounds {D w U z S} (J:DualWord D w U S) (M:StrongMarks D w U z S)
    (hU:U.Nonempty) :
    2*(J.u₀-shift)+(J.u₁-J.u₀)=width D ∧
    ∀ γ∈U,(J.Q γ).natDegree≤J.u₀-shift ∧
      (J.P γ).natDegree≤(J.u₀-shift)+(J.u₁-J.u₀) := by
  obtain ⟨γ,hγ⟩:=hU
  have h0:=(J.degree γ hγ).1
  have hA:=M.strong γ hγ
  have hs :=J.order
  have hw:=J.gMz
  have ha :farAgreement+shift=P6.dw:= by decide
  refine ⟨?_,fun β hβ => ?_⟩
  · unfold width
    omega
  · have hA' := M.strong β hβ
    obtain ⟨_,hQ,hP⟩:=J.degree β hβ
    omega
def BelowAt (F:Dg) (u s W:ℕ) :Prop :=
  ∀ i j,(F.coeff i).coeff j≠0 →
    ((F.coeff i).coeff j).natDegree+F.natDegree*u+i*s≤W
def Witness (D l:ℕ) (x :NativeWitness) :Prop :=
  let B:=width D
  let E :=l+x.g
  let M:=x.W+1+x.j*B
  x.j≤x.g∧l*B≤x.W∧E*B<M ∧
  (x.c+1)*(B*E*(E+1)/2+B*x.j*(x.j+1)/2)<(x.g+1)*x.c*M ∧
  (2*l-2)*x.W-l*(l-1)*B<p
abbrev pole (D l:ℕ) (x :NativeWitness) :=
  (6*l-4)*x.W-(3*l*l-4*l+2)*width D
abbrev lowPrice (D l:ℕ) (x :NativeWitness) :=
  exclusions l*gap D + nodeRate l*blockLength+pole D l x
abbrev linearPrice :=2*blockLength
def jX (D l:ℕ) (x :NativeWitness) :=
  if l=1 then linearPrice else max (lowPrice D l x) (highRate l x*gap D)
def Guards (D e rate :ℕ) :Prop :=
  gap D ≤ rate ∧ ∀ l,1≤l→l≤e →
    ∃ x :NativeWitness,(l=1∨Witness D l x)∧jX D l x≤ rate
def NodeBound (e :ℕ) :Prop :=
  ∀ (F:Dg) (l h:ℕ),l≤e→EquationBounds F l h →
    ∀ (S:Sections F) (x a b:L),a≠0∨b≠0 →
      (S.CF.filter fun γ =>
        (S.P γ).eval x*a=(S.Q γ).eval x*b∧(S.A γ).eval x≠0).card≤nodeRate l*h
def PoleBound (B e :ℕ) :Prop :=
  ∀ (F:Dg) (l h u s W:ℕ),l≤e→EquationBounds F l h →
    2*u+s=B→l*B≤W→HE F s (W-l*u) →
    (2*l-2)*W-l*(l-1)*B<p →
    ∀ S:Sections F,
      ∑ γ∈S.CF,max (S.B γ).natDegree ((S.A γ).natDegree-pN S s γ) ≤
        ((6*l-4)*W-(3*l*l-4*l+2)*B)*h
end
end qXdgDRd
end
