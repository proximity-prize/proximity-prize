import ProximityPrize.SubmissionLower.ZGDv7Ub
import ProximityPrize.SubmissionLower.ZAsXn9b
import ProximityPrize.SubmissionLower.ZW8Nc6b
import ProximityPrize.SubmissionLower.ZZpExZa
set_option Elab.async false
open _root_ renaming IsFractionRing.injective → zxb, Polynomial.ext → zXJ, Polynomial.map_injective → zTo, Polynomial.map_zero → zgY, PowerSeries.C → zMG, RingHom.comp_apply → zQb, RingHom.comp_assoc → zxS, RingHom.congr_fun → zLs
section
set_option backward.isDefEq.respectTransparency false
namespace qklsuQd
noncomputable section
open Polynomial
open P5 (K)
open cu (L)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open qb0hmCe (CurveModel)
open qxPDCsa (References RadicalOf BoundedAt finiteRef)
open qqV3gre (seedDiff physicalDerivative)
open qoGY3we (reduce a8p physDiff)
open q2TwyLa (i5 aQ lift integral diffPoly)
open qU1uHGd (lift_embed lift_jet)
open private diff_incl from ProximityPrize.SubmissionLower.ZGDv7Ub
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private bound_at from ProximityPrize.SubmissionLower.Zay1XCa
open private sheet_discr_bound from ProximityPrize.SubmissionLower.ZW8Nc6b
open private efc aMX from ProximityPrize.SubmissionLower.Y
open scoped WithZero
theorem multiplier_at {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
   {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
   (A:References V D W) {t:Cq.E[X]}
   (ht:RadicalOf (F.f.discr*finiteRef F (A.a 0)*finiteRef F (A.a 1)) t)
   (γ:K) (hγ:γ∈F.marks) :
   ∀ j,(Valued.v :Valuation aQ ℤᵐ⁰) (F.atPlace γ hγ (t.coeff j))≤1 := by
 let w:=(F.place γ).value
 have hmul {g h:Cq.E[X]} (hg:BoundedAt w g 1) (hh:BoundedAt w h 1) :
     BoundedAt w (g*h) 1 := by
   intro j
   have he (f :Cq.E[X]) (hf :BoundedAt w f 1) :efc w f≤1 :=
     Finset.sup_le fun i _=>hf i
   apply (aMX w _ j).trans
   change efc w (g*h)≤1
   rw [map_mul]
   exact (mul_le_mul' (he g hg) (he h hh)).trans_eq (mul_one _)
 have h:=ht.bound w 1 (hmul (hmul (bound_at (sheet_discr_bound F) hγ)
   (bound_at (A.finite_bound 0) hγ)) (bound_at (A.finite_bound 1) hγ))
 intro j
 rw [← F.value γ hγ]
 exact h j
theorem lift_multiplier {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] aQ)
   (t:E[X]) (ht : ∀ j,(Valued.v :Valuation aQ ℤᵐ⁰) (a (t.coeff j))≤1) :
   ∃ T:i5[X],T.map a8p=t.map a.toRingHom ∧
     reduce T=qxPDCsa.reduce a t:= by
 have hC:integral a (C t) := by
   intro i j
   by_cases hi:i=0
   · simpa [hi] using ht j
   · simp [coeff_C,hi]
 refine ⟨(lift a (C t) hC).coeff 0,?_,?_⟩
 · have h:=congrArg (fun g:aQ[X][X]=>g.coeff 0) (lift_embed a (C t) hC)
   simp only [q1kuFjb.mapTwice,coeff_map,coe_mapRingHom,coeff_C_zero] at h
   exact h
 · have h:=congrArg (fun g:L[X][X]=>g.coeff 0) (lift_jet a (C t) hC).1
   simp only [q1kuFjb.mapTwice,coeff_map,coe_mapRingHom] at h
   exact h
theorem multiplier_diff (t:i5[X]) : (diffPoly t).map a8p=seedDiff (t.map a8p) := by
 apply zXJ
 intro i
 rw [coeff_map,diffPoly,sum_coeff _ (map_zero _),seedDiff,sum_coeff _ (map_zero _),coeff_map]
 exact diff_incl _
theorem physical_diff (f :i5[X][X]) :
  (physDiff f).map (mapRingHom a8p)=physicalDerivative (f.map (mapRingHom a8p)) := by
 apply zXJ
 intro i
 rw [coeff_map,physDiff,sum_coeff _ (by simp),physicalDerivative,sum_coeff _ (by simp),coeff_map]
 exact (derivative_map _ _).symm
end
end qklsuQd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qklsuQd
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys)
open qqV3gre
open qoGY3we (Series bY a8p)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
abbrev Complete :=LaurentSeries FX
abbrev intoComplete :Series →+* Complete :=HahnSeries.ofPowerSeries ℤ FX
abbrev intoSeed :aQ →+* Complete :=
 { toFun:= fun a=>a.map (algebraMap L FX)
   map_zero' := HahnSeries.map_zero (algebraMap L FX).toZeroHom
   map_one' := HahnSeries.map_one (algebraMap L FX).toMonoidWithZeroHom
   map_add' := fun _ _=>HahnSeries.map_add (algebraMap L FX).toAddMonoidHom
   map_mul' := fun _ _=>HahnSeries.map_mul (algebraMap L FX).toNonUnitalRingHom }
def coeffComplete :aQ[X] →+* Complete :=
 eval₂RingHom intoSeed (HahnSeries.C (phys Polynomial.X))
private theorem coeffComplete_inj:Function.Injective coeffComplete := by
 apply (injective_iff_map_eq_zero coeffComplete).mpr
 intro f h
 have he (n:ℤ) : (coeffComplete f).coeff n=phys (f.sum fun i a=>monomial i (a.coeff n)) := by
   simp only [coeffComplete,coe_eval₂RingHom,eval₂_eq_sum,Polynomial.sum_def,
     HahnSeries.coeff_sum,map_sum]
   apply Finset.sum_congr rfl
   intro i _
   rw [← (HahnSeries.C:FX →+* Complete).map_pow,HahnSeries.C_apply,
     HahnSeries.coeff_mul_single_zero]
   change algebraMap L FX ((f.coeff i).coeff n)*phys (Polynomial.X:L[X])^i= _
   rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
   rw [IsScalarTower.algebraMap_apply L L[X] FX]
   rfl
 apply zXJ
 intro i
 rw [coeff_zero]
 apply HahnSeries.ext
 funext n
 have hn:=he n
 rw [h,HahnSeries.coeff_zero] at hn
 have hz :=(zxb L[X] FX) (hn.symm.trans (map_zero phys).symm)
 rw [← sum_coeff (fun a :aQ=>a.coeff n) (by simp),hz,coeff_zero,
   HahnSeries.coeff_zero]
theorem coeff_complete_series :
   coeffComplete.comp (mapRingHom a8p)=intoComplete.comp (bY false) := by
 apply Polynomial.ringHom_ext
 · intro a
   simp only [zQb,coe_mapRingHom,map_C,coeffComplete,bY,
    coe_eval₂RingHom,eval₂_C]
   apply HahnSeries.ext
   funext n
   change algebraMap L FX ((a :aQ).coeff n) =
    ((PowerSeries.map (algebraMap L FX) a :Series) :Complete).coeff n
   by_cases hn:n<0 <;> simp [PowerSeries.coeff_coe,hn]
 · simp [coeffComplete,bY,intoComplete,HahnSeries.ofPowerSeries_C]
private abbrev top:Complete →+* AlgebraicClosure Complete :=algebraMap _ _
private theorem over_roots : ∃ e :EC →+* AlgebraicClosure Complete,
  e.comp physicalCoeff=top.comp coeffComplete := by
 let j:PhysicalField →+* Complete :=IsFractionRing.lift coeffComplete_inj
 let k :=top.comp j
 let:Algebra PhysicalField (AlgebraicClosure Complete) :=k.toAlgebra
 let e :EC →ₐ[PhysicalField] AlgebraicClosure Complete :=IsAlgClosed.lift
 refine ⟨e.toRingHom,RingHom.ext fun a => ?_⟩
 change e (algebraMap PhysicalField EC (algebraMap aQ[X] PhysicalField a)) =
  top (coeffComplete a)
 rw [e.commutes]
 change top (j (algebraMap aQ[X] PhysicalField a))= _
 rw [IsFractionRing.lift_algebraMap]
private theorem lift_root_image {f :aQ[X][X]} (hf :f≠0)
   {y :Complete} (hy :f.eval₂ coeffComplete y=0)
   (e :EC →+* AlgebraicClosure Complete) (he :e.comp physicalCoeff=top.comp coeffComplete) :
   ∃ x :EC,f.eval₂ physicalCoeff x=0∧e x=top y := by
 let g:=f.map physicalCoeff
 have hp:=(algebraMap PhysicalField EC).injective.comp
   (zxb aQ[X] PhysicalField)
 have hne :g≠0:= by
   change (mapRingHom physicalCoeff) f≠0
   exact (map_ne_zero_iff (mapRingHom physicalCoeff) (zTo physicalCoeff hp)).mpr hf
 have hz : (g.map e).eval (top y)=0:= by
   rw [show g.map e=f.map (e.comp physicalCoeff) from map_map _ _ _,he,eval_map,
     ← hom_eval₂,hy,map_zero]
 have hng:g.map e≠0:= by
   intro h
   exact hne (zTo e e.injective (h.trans (zgY _).symm))
 have hm:=(mem_roots hng).2 hz
 rw [(IsAlgClosed.splits g).roots_map_of_injective e.injective] at hm
 obtain ⟨x,hx,heq⟩:=Multiset.mem_map.mp hm
 exact ⟨x,by simpa only [g,eval_map,IsRoot] using isRoot_of_mem_roots hx,heq⟩
def completeCuts (f :aQ[X][X]) (t:aQ[X]) (u v :L) (y :Complete) :
    Complete×Complete :=
  let ev (g:aQ[X][X]) :=g.eval₂ coeffComplete y
  let s := -(ev (qziIa4d.seedDerivative f)/ev f.derivative)
  let x := -(ev (physicalDerivative f)/ev f.derivative)
  let l:=(y - coeffComplete (C (algebraMap L aQ u)))⁻¹ -
    (y - coeffComplete (C (algebraMap L aQ v)))⁻¹
  (coeffComplete t*(s*l),
    coeffComplete t.derivative*(s*l) - coeffComplete (seedDiff t)*(x*l))
theorem integral_transfer {f :aQ[X][X]} {t:aQ[X]} {u v :L}
   (hf :f≠0) (h:integralLogs integralCoeff f t u v)
   (y s₁ s₂:Series) (hy :f.eval₂ coeffComplete (intoComplete y)=0)
   (hs :completeCuts f t u v (intoComplete y)=(intoComplete s₁,intoComplete s₂)) :
   (bY false).IsIntegralElem s₁∧(bY false).IsIntegralElem s₂:= by
 obtain ⟨e,he⟩:=over_roots
 obtain ⟨x,hx,hx'⟩:=lift_root_image hf hy e he
 have hlog :
     e (logCuts f t u v x).1=top (completeCuts f t u v (intoComplete y)).1 ∧
     e (logCuts f t u v x).2=top (completeCuts f t u v (intoComplete y)).2 := by
   have hcoeff (a :aQ[X]) :e (physicalCoeff a)=top (coeffComplete a) :=
     zLs he a
   simp only [logCuts,completeCuts,constant,map_mul,map_sub,map_neg,map_div₀,map_inv₀,
     hom_eval₂,hx',he,hcoeff,and_self]
 rw [hs] at hlog
 have hc:e.comp integralCoeff=(top.comp intoComplete).comp (bY false) := by
   rw [integralCoeff,← zxS,he,zxS]
   change top.comp (coeffComplete.comp (mapRingHom a8p))= _
   rw [coeff_complete_series,zxS]
 have pass (s :Series) (x :EC) (hs :e x=top (intoComplete s))
     (hI:integralCoeff.IsIntegralElem x) : (bY false).IsIntegralElem s := by
   apply RingHom.IsIntegralElem.of_map (g:=top.comp intoComplete)
     (top.injective.comp HahnSeries.ofPowerSeries_injective)
   rw [← hc]
   exact hs ▸ hI.map e
 exact ⟨pass _ _ hlog.1 (h x hx).1,pass _ _ hlog.2 (h x hx).2⟩
end
end qklsuQd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qklsuQd
noncomputable section
open Polynomial
open cu (L FX j9)
open P5_7_7 (phys)

open qrezXJe (rootEval)
open qoGY3we (Series a8p bY reduce cc physDiff seedTangent local_root integral_reduce)
open q2TwyLa (i5 integral lift diff diffPoly)
open qqV3gre (integralLogs integralCoeff arcEquation)
open qU1uHGd (lift_embed lift_jet diff_embed)
open private reduce_eval differentiated_root from ProximityPrize.SubmissionLower.ZAsXn9b
open private clear_den phys_ne from ProximityPrize.SubmissionLower.ZSm5aLa
open scoped WithZero
private theorem inv_complete {a :Series} (ha :cc a≠0) :
  intoComplete a⁻¹=(intoComplete a)⁻¹:= by
 have h:=congrArg intoComplete (PowerSeries.inv_mul_cancel a ha)
 rw [map_mul,map_one] at h
 have hne :intoComplete a≠0:=(map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).2
  (fun hz=>ha (by rw [hz,map_zero]))
 rw [← one_div (intoComplete a),eq_div_iff hne]
 exact h
private theorem constant_complete (u:L) :
  coeffComplete (C (algebraMap L (LaurentSeries L) u))=intoComplete (zMG (phys (C u))) := by
 have hu:a8p (zMG u)=algebraMap L (LaurentSeries L) u:= by
  rw [LaurentSeries.algebraMap_apply]
  exact PowerSeries.coe_C u
 have h:=zLs coeff_complete_series (C (zMG u))
 simp only [zQb,coe_mapRingHom,map_C,bY,coe_eval₂RingHom,eval₂_C,
  PowerSeries.map_C,hu] at h
 exact h
private theorem ratio_factor {P:L[X]} {u v :L} (huv :u≠v)
   (hu:phys (P - C u)≠0) (hv :phys (P - C v)≠0) :
   ((phys (P - C u))⁻¹-(phys (P - C v))⁻¹) *
     phys ((P - C u)*(P - C v)*C (u-v)⁻¹)=1 := by
 have hc:phys (C (u-v)⁻¹)=(phys (C (u-v)))⁻¹ :=
   map_inv₀ (algebraMap L FX) (u-v)
 have hd:phys (C (u-v))=phys (P - C v) - phys (P - C u) := by
   rw [← map_sub,map_sub C]
   congr 1
   abel
 have hn:phys (P - C v) - phys (P - C u)≠0:=hd ▸
   phys_ne (C_ne_zero.mpr (sub_ne_zero.mpr huv))
 rw [map_mul,map_mul,hc,hd]
 field_simp [hu,hv,hn]
private theorem specialize_cuts (f :i5[X][X]) (T:i5[X]) (u v :L) (P N B:L[X])
    (hf :f.map (mapRingHom a8p)≠0)
    (hr :rootEval (f.map reduce) P=0)
    (hd:rootEval (f.map reduce).derivative P≠0)
    (hu:P≠C u) (hv :P≠C v) (huv :u≠v)
    (hB:B≠0) (hcop:IsCoprime N B) (hN :phys N/phys B=seedTangent f P)
    (hlog:integralLogs integralCoeff (f.map (mapRingHom a8p)) (T.map a8p) u v) :
    B∣reduce T∧B∣(reduce T).derivative := by
  obtain ⟨J⟩:=local_root f u P hr hd (sub_ne_zero.mpr hu)
  let ev (g:i5[X][X]) :=g.eval₂ (bY false) J.y
  let d:=ev f.derivative
  let U:=J.y-PowerSeries.C (phys (C u))
  let V:=J.y-PowerSeries.C (phys (C v))
  let l:=U⁻¹-V⁻¹
  let a := -(ev (diff f))*d⁻¹
  let b := -(ev (physDiff f))*d⁻¹
  have hd0:cc d=rootEval (f.map reduce).derivative P:= by
    change cc (f.derivative.eval₂ (bY false) J.y)= _
    rw [reduce_eval _ _ _ J.reduce_y,derivative_map]
  have hu0:cc U=phys (P - C u) := by simp [U,J.reduce_y]
  have hv0:cc V=phys (P - C v) := by simp [V,J.reduce_y]
  have hU:=phys_ne (sub_ne_zero.mpr hu)
  have hV:=phys_ne (sub_ne_zero.mpr hv)
  let s :=bY false T*(a*l)
  let t:=bY false T.derivative*(a*l) - bY false (diffPoly T)*(b*l)
  have evL (g:i5[X][X]) : (g.map (mapRingHom a8p)).eval₂ coeffComplete (intoComplete J.y) =
      intoComplete (ev g) := by
    change _=intoComplete (g.eval₂ (bY false) J.y)
    rw [eval₂_map,coeff_complete_series,hom_eval₂]
  have cL (g:i5[X]) :coeffComplete (g.map a8p)=intoComplete (bY false g) :=
    zLs coeff_complete_series g
  have hroot : (f.map (mapRingHom a8p)).eval₂ coeffComplete (intoComplete J.y)=0:= by
    rw [evL,show ev f=0 from J.root,map_zero]
  have hcut:completeCuts (f.map (mapRingHom a8p)) (T.map a8p) u v (intoComplete J.y) =
      (intoComplete s,intoComplete t) := by
    dsimp only [completeCuts]
    have hseed : (diff f).map (mapRingHom a8p) =
        qziIa4d.seedDerivative (f.map (mapRingHom a8p)) :=diff_embed f
    rw [← hseed,← physical_diff f,← multiplier_diff T,
      derivative_map f (mapRingHom a8p),derivative_map T a8p]
    simp only [evL,cL,constant_complete,s,t,a,b,l,
      map_mul,map_sub,map_neg,inv_complete (hd0 ▸ hd),
      inv_complete (hu0 ▸ hU),inv_complete (hv0 ▸ hV),div_eq_mul_inv,neg_mul]
    simp only [d,U,V,map_sub]
    congr 1 <;> ring
  obtain ⟨h₁,h₂⟩:=integral_transfer hf hlog J.y s t hroot hcut
  obtain ⟨Q₁,hQ₁⟩:=integral_reduce h₁
  obtain ⟨Q₂,hQ₂⟩:=integral_reduce h₂
  have ha :cc a=phys N/phys B:= by
    rw [hN]
    simp only [a,ev,map_mul,map_neg,PowerSeries.constantCoeff_inv,hd0,
      reduce_eval _ _ _ J.reduce_y,seedTangent,div_eq_mul_inv,neg_mul]
  have hb:cc b=phys P.derivative := by
    simp only [b,ev,map_mul,map_neg,PowerSeries.constantCoeff_inv,hd0,
      reduce_eval _ _ _ J.reduce_y]
    rw [differentiated_root f P hr,mul_comm,← mul_assoc,inv_mul_cancel₀ hd,one_mul]
  let H :=(P - C u)*(P - C v)*C (u-v)⁻¹
  have hl:cc l*phys H=1 := by
    simpa only [l,map_sub,PowerSeries.constantCoeff_inv,hu0,hv0,H] using ratio_factor huv hU hV
  have hc (g:i5[X]) :cc (bY false g)=phys (reduce g) :=
    zLs qoGY3we.finite_reduce g
  simp only [s,t,map_mul,map_sub,hc,ha,hb] at hQ₁ hQ₂
  have hder :reduce T.derivative=(reduce T).derivative :=(derivative_map _ _).symm
  rw [hder] at hQ₂
  constructor
  · apply clear_den hB hcop
    refine ⟨Q₁*H,?_⟩
    rw [map_mul,hQ₁,mul_assoc,mul_assoc,hl,mul_one]
  · apply clear_den hB hcop
    refine ⟨Q₂*H+reduce (diffPoly T)*P.derivative,?_⟩
    rw [map_add,map_mul phys Q₂ H,map_mul phys (reduce (diffPoly T)) P.derivative,hQ₂,sub_mul]
    simp only [mul_assoc,hl,mul_one,sub_add_cancel]
theorem proof :qqV3gre.c3:= by
 intro q Cq z S F V D W A t ht γ hγ _ a hlog
 let P:=j9 (S γ)
 have hi:integral a F.f := by
   intro i j
   change (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
     (F.atPlace γ (V.Bp hγ) ((F.f.coeff i).coeff j))≤1
   rw [← F.value γ (V.Bp hγ)]
   exact F.integral γ (V.Bp hγ) i j
 let f :=lift a F.f hi
 have he :f.map (mapRingHom a8p)=arcEquation a F.f :=lift_embed a F.f hi
 obtain ⟨h₀,h₁⟩:=lift_jet a F.f hi
 change f.map reduce= _ at h₀
 change (diff f).map reduce= _ at h₁
 obtain ⟨T,hT,hrT⟩:=lift_multiplier a t (multiplier_at A ht γ (V.Bp hγ))
 rw [← hrT]
 apply specialize_cuts f T (A.a 0) (A.a 1) P (V.num γ)
 · rw [he,arcEquation]
   intro hz
   exact F.irreducible.ne_zero ((zTo _ (zTo _ a.injective))
     (hz.trans (zgY _).symm))
 · rw [h₀]
   exact F.root γ (V.Bp hγ)
 · rw [h₀]
   exact V.simple γ hγ
 · exact A.avoids γ hγ 0
 · exact A.avoids γ hγ 1
 · exact fun h=>(by decide : (0:Fin 2)≠1) (A.finite_distinct h)
 · exact V.den_ne γ hγ
 · exact V.reduced γ hγ
 · rw [seedTangent,h₀,h₁]
   exact V.formula γ hγ
 · rwa [he,hT]
end
end qklsuQd
end
