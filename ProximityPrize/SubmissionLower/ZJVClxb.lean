import ProximityPrize.SubmissionLower.Z4nC3pd
import ProximityPrize.SubmissionLower.ZnTmQ9b
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qJm9rWb
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K)
open cu (L)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (tu Pencil evalXY dx coords linear)
open qfzuawb (SimpleFiber map₂ KT P5 pencilForm)
open qZu9hjc (atPair jacobian)
private abbrev ev {E M:Type} [CommRing E] [CommRing M] (j:E →+* M) (x y :M) :
 E[X][X] →+* M:=eval₂RingHom (eval₂RingHom j x) y
private theorem at_map {E B M:Type} [CommRing E] [CommRing B] [CommRing M]
   (j:E →+* B) (k :B →+* M) (x y :M) (f :E[X][X]) :
   ev k x y (map₂ j f)=ev (k.comp j) x y f := by
 change (ev k x y).comp (map₂ j) f=ev (k.comp j) x y f
 suffices (ev k x y).comp (map₂ j)=ev (k.comp j) x y by rw [this]
 apply Polynomial.ringHom_ext
 · intro r
   simpa only [RingHom.comp_apply,map₂,coe_mapRingHom,map_C,ev,
     coe_eval₂RingHom,eval₂_C] using (eval₂_map (p:=r) j k x)
 · simp [ev,map₂]
private theorem at_embed {B M Ω:Type} [Field B] [Field M] [Field Ω]
   [Algebra B M] [Algebra B Ω] (σ:M →ₐ[B] Ω) (x y :M) (f :B[X][X]) :
   atPair (algebraMap B Ω) (σ x) (σ y) f =
     σ (atPair (algebraMap B M) x y f) := by
 change f.eval₂ (eval₂RingHom (algebraMap B Ω) (σ x)) (σ y) =
   σ.toRingHom (f.eval₂ (eval₂RingHom (algebraMap B M) x) y)
 rw [hom_eval₂]
 congr 1
 apply Polynomial.ringHom_ext
 · intro b
   have h:σ.toRingHom.comp (algebraMap B M)=algebraMap B Ω :=
     RingHom.ext σ.commutes
   simpa only [coe_eval₂RingHom,eval₂_C,RingHom.comp_apply]
     using (RingHom.congr_fun h b).symm
 · simp
private theorem dx_map {E B:Type} [Field E] [Field B] (j:E →+* B) (f :E[X][X]) :
  dx (map₂ j f)=map₂ j (dx f) := by
 ext i:1
 simp only [bXI,map₂,coe_mapRingHom,coeff_map,derivative_map]
private theorem dy_map {E B:Type} [Field E] [Field B] (j:E →+* B) (f :E[X][X]) :
  (map₂ j f).derivative=map₂ j f.derivative :=
 derivative_map f (mapRingHom j)
private theorem dx_linear {B:Type} [Field B] (c:B) (a b:B[X][X]) :
  dx (b - C (C c)*a)=dx b - C (C c)*dx a := by
 ext i:1
 simp only [bXI,coeff_sub,coeff_C_mul,derivative_sub,derivative_C_mul]
private theorem dy_linear {B:Type} [Field B] (c:B) (a b:B[X][X]) :
  (b - C (C c)*a).derivative=b.derivative - C (C c)*a.derivative := by
 rw [derivative_sub,derivative_C_mul]
private theorem aHH {E M:Type} [Field E] [Field M] [Algebra L E] [Algebra E M]
   (f :E[X][X]) (a :Fin 4→L) (x y :M) :
   evalXY (P5 f a) x y =
     linear ((algebraMap E M).comp (algebraMap L E)) a (coords f x y) := by
 change ev (algebraMap E M) x y (∑ i,C (C (algebraMap L E (a i)))*KT f i)= _
 rw [map_sum,linear]
 apply sum_congr rfl
 intro i _
 rw [map_mul]
 have hc (b:E) :ev (algebraMap E M) x y (C (C b))=algebraMap E M b:= by
   simp [ev]
 rw [hc,RingHom.comp_apply]
 congr 1
 fin_cases i <;> simp [KT,coords,evalXY,ev]
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
private theorem fiber_at (A:Pencil F) :
    let j:=algebraMap Cq.E[X] (tu Cq.E)
    let f :=map₂ j (map₂ C F.f)
    let g:=map₂ j (pencilForm A)
    let Q:=map₂ j (map₂ C F.f.derivative)
    let i:=algebraMap (tu Cq.E) A.M
    atPair i A.x A.y f=0∧atPair i A.x A.y g=0 ∧
      jacobian i A.x A.y f g≠0∧atPair i A.x A.y Q=A.polar := by
  let E :=Cq.E
  let B:=tu E
  let j:=algebraMap E[X] B
  let i:=algebraMap B A.M
  let u:=j (Polynomial.X:E[X])
  let a :=P5 F.f A.a
  let b:=P5 F.f A.b
  let m (r :E[X][X]) :=map₂ j (map₂ C r)
  let g:=map₂ j (pencilForm A)
  let evE (r :E[X][X]) :=evalXY r A.x A.y
  let evB (r :B[X][X]) :=atPair i A.x A.y r
  change evB (m F.f)=0∧evB g=0 ∧
    jacobian i A.x A.y (m F.f) g≠0∧evB (m F.f.derivative)=A.polar
  have hi: (i.comp j).comp C=algebraMap E A.M:= by
    ext c
    change i (j (C c))=algebraMap E A.M c
    rw [Polynomial.C_eq_algebraMap,← IsScalarTower.algebraMap_apply E E[X] B,
      ← IsScalarTower.algebraMap_apply E B A.M]
  have hm (r :E[X][X]) :evB (m r)=evE r := by
    change ev i A.x A.y (map₂ j (map₂ C r))= _
    rw [at_map j i A.x A.y (map₂ C r),at_map C (i.comp j) A.x A.y r,hi]
    rfl
  have hg:g=m b - C (C u)*m a := by
    change map₂ j (pencilForm A)= _
    rw [pencilForm,map_sub (map₂ j),map_mul (map₂ j)]
    have hc:map₂ j (C (C (Polynomial.X:E[X])))=C (C u) := by simp [map₂,u]
    rw [hc]
  have hdx (r :E[X][X]) :dx (m r)=m (dx r) := by
    simpa only [m,map₂,coe_mapRingHom,Polynomial.map_map,mapRingHom_comp]
      using dx_map (j.comp C) r
  have hdy (r :E[X][X]) : (m r).derivative=m r.derivative := by
    simpa only [m,map₂,coe_mapRingHom,Polynomial.map_map,mapRingHom_comp]
      using dy_map (j.comp C) r
  have he (r s :B[X][X]) :evB (r - C (C u)*s)=evB r - A.u*evB s := by
    change ev i A.x A.y (r - C (C u)*s) =
      ev i A.x A.y r - i u*ev i A.x A.y s
    rw [map_sub,map_mul]
    simp only [coe_eval₂RingHom,eval₂_C]
  have hv :evE b=A.u*evE a := by
    dsimp only [evE,a,b]
    rw [aHH,aHH]
    exact A.value
  have ha :evE a≠0:= by
    dsimp only [evE,a]
    rw [aHH]
    exact A.gauge_ne
  refine ⟨(hm _).trans A.equation,?_,?_,hm _⟩
  · rw [hg,he,hm,hm,hv,sub_self]
  · let _:=A.separable
    obtain ⟨D,hD,hu⟩:=pencil_derivation (E :=E) (M:=A.M)
    change D A.u=1 at hu
    have hc (r :E[X][X]) :
        D (evE r)=evE (dx r)*D A.x+evE r.derivative*D A.y :=
      directional D hD _ _ _
    have hf :=hc F.f
    have hroot :evE F.f=0:=A.equation
    rw [hroot,map_zero] at hf
    have hb:=congrArg D hv
    rw [hc b,D.leibniz,hc a,hu,smul_eq_mul,smul_eq_mul,mul_one] at hb
    intro hz
    change evB (dx (m F.f))*evB g.derivative -
      evB (m F.f).derivative*evB (dx g)=0 at hz
    rw [hdx,hdy,hg,dx_linear,dy_linear,hdx,hdx,hdy,hdy,he,he,
      hm,hm,hm,hm,hm,hm] at hz
    have hn:evE F.f.derivative≠0:=A.polar_ne
    apply ha
    apply (mul_eq_zero.mp (_:evE F.f.derivative*evE a=0)).resolve_left hn
    linear_combination -(evE F.f.derivative)*hb -
      (evE b.derivative - A.u*evE a.derivative)*hf - D A.x*hz
theorem fiber :qfzuawb.c3:= by
 intro q Cq z S F A
 let E :=Cq.E
 let B:=tu E
 let Ω:=AlgebraicClosure B
 let j:=algebraMap E[X] B
 let f :=map₂ j (map₂ C F.f)
 let g:=map₂ j (pencilForm A)
 let Q:=map₂ j (map₂ C F.f.derivative)
 let _:=A.separable
 let _:Infinite B:=Infinite.of_injective j (IsFractionRing.injective E[X] B)
 let H :=A.M →ₐ[B] Ω
 let e :=(Fintype.equivFin H).symm
 let point (k :Fin (Fintype.card H)) :Ω×Ω:=(e k A.x,e k A.y)
 obtain ⟨hf,hg,hs,hQ⟩:=fiber_at A
 change Nonempty (SimpleFiber f g Q A.polarPoly)
 refine ⟨⟨_,point,?_,?_,?_,?_,?_⟩⟩
 · intro k l h
   apply e.injective
   have hx :e k A.x=e l A.x :=congrArg Prod.fst h
   have hy :e k A.y=e l A.y :=congrArg Prod.snd h
   apply AlgHom.ext
   intro r
   have hr :r∈IntermediateField.adjoin E ({A.x,A.y} : Set A.M) := by
     rw [A.generates]
     trivial
   refine IntermediateField.adjoin_induction E
     (p:= fun r _=>e k r=e l r) ?_ ?_ ?_ ?_ ?_ hr
   · intro x hx'
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx'
     rcases hx' with rfl | rfl
     · exact hx
     · exact hy
   · intro c
     rw [IsScalarTower.algebraMap_apply E B A.M]
     exact ((e k).commutes _).trans ((e l).commutes _).symm
   · intro a b _ _ ha hb
     rw [map_add,map_add,ha,hb]
   · intro a _ ha
     rw [map_inv₀,map_inv₀,ha]
   · intro a b _ _ ha hb
     rw [map_mul,map_mul,ha,hb]
 · intro k
   change atPair (algebraMap B Ω) (e k A.x) (e k A.y) f=0
   rw [at_embed,hf,map_zero]
 · intro k
   change atPair (algebraMap B Ω) (e k A.x) (e k A.y) g=0
   rw [at_embed,hg,map_zero]
 · intro k
   change jacobian (algebraMap B Ω) (e k A.x) (e k A.y) f g≠0
   rw [jacobian]
   simp only [at_embed (e k) A.x A.y,← map_mul,← map_sub]
   exact (map_ne_zero_iff (e k) (e k).injective).mpr hs
 · change atPair (algebraMap B A.M) A.x A.y Q=A.polar at hQ
   rw [Pencil.polarPoly,charpoly_embeddings]
   symm
   apply Fintype.prod_equiv e
   intro k
   dsimp only [point]
   rw [at_embed (e k) A.x A.y Q,hQ]
end
end qJm9rWb
