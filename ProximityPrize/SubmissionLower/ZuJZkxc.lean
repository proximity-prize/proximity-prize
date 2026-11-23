import ProximityPrize.SubmissionLower.ZitKCce
import ProximityPrize.SubmissionLower.ZRfXqSb
import ProximityPrize.SubmissionLower.ZULJdud
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZFAtzgb
import ProximityPrize.SubmissionLower.ZK8GpQb
import ProximityPrize.SubmissionLower.ZPZNNwd
import ProximityPrize.SubmissionLower.ZhlCjsa
import ProximityPrize.SubmissionLower.ZfSxMva
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Function.Injective → zq4, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_apply → zG3, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.ringHom_ext → zXT, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_right → zIu, Nat.sub_zero → zPv, Polynomial.X → z7y, Polynomial.map_sum → zWe, PowerSeries.constantCoeff → zbO, RingHom.comp_apply → zQb, RingHom.id → zz4
section
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace q8hd3Fb
noncomputable section
open Polynomial
open cu (L)
open qZu9hjc (atPair)
open q8Z6NHc (jo Generic Index UniversalValue form genericF genericG)
open qG7TGJa (aFB value)
open qFwMjQd (onLine)
open q33Mraa (Lw scaleSlope scaleLine pointValue)
open private atPair_hom from ProximityPrize.SubmissionLower.ZitKCce
variable {d s a :ℕ} {b c:L}
local notation "D" => jo d s a
local notation "K₀" => aFB d s a
local notation "E" => Generic d s a
local notation "j" => algebraMap D E
private def weight (l:L) :Index d s a→L
 | .inl _=>l
 | .inr _=>1
private def scale (l:L) :D →+* D :=
 zOD znf
  (fun i=>znf (weight l i)*z9v i)
@[simp] private theorem coC (l x :L) :
   scale (d:=d) (s :=s) (a :=a) l (znf x)=znf x :=
  zTv _ _ _
@[simp] private theorem scale_X (l:L) (i:Index d s a) :
   scale l (z9v i)=znf (weight l i)*z9v i :=
  zrD _ _ _
private theorem scale_comp {l m:L} (h:m*l=1) :
   (scale (d:=d) (s :=s) (a :=a) l).comp (scale m)=zz4 D:= by
 apply zXT
 · intro x
   simp
 · intro i
   rw [zQb,RingHom.id_apply,scale_X,map_mul,coC,scale_X,
     ← mul_assoc,← map_mul]
   cases i <;> simp [weight,h]
private def scaleEquiv (l:L) (hl:l≠0) :E ≃+* E :=
 let e :D ≃+* D:=RingEquiv.ofRingHom (scale l) (scale l⁻¹)
  (scale_comp (inv_mul_cancel₀ hl)) (scale_comp (mul_inv_cancel₀ hl))
 IsAlgClosure.equivOfEquiv E E (IsFractionRing.ringEquivOfRingEquiv (K:=K₀) (L:=K₀) e)
private theorem scaleEquiv_coeff (l:L) (hl:l≠0) (x :D) :
  scaleEquiv l hl (j x)=j (scale l x) := by
 simp only [scaleEquiv,zG3 D K₀ E,
  IsAlgClosure.equivOfEquiv_algebraMap,IsFractionRing.ringEquivOfRingEquiv_algebraMap]
 rfl
private theorem base_fixed (l:L) (hl:l≠0) (x :L) :
  scaleEquiv (d:=d) (s :=s) (a :=a) l hl (algebraMap L E x)=algebraMap L E x := by
 rw [zG3 L D E]
 change scaleEquiv l hl (j (znf x))=j (znf x)
 rw [scaleEquiv_coeff,coC]
private theorem slot_scaled (l:L) (hl:l≠0) (i:Index d s a) :
  scaleEquiv l hl (Lw i)=algebraMap L E (weight l i)*Lw i:= by
 rw [Lw,scaleEquiv_coeff,scale_X,map_mul]
 rfl
private theorem f_scaled (l:L) (hl:l≠0) :
   (genericF d s a).map (mapRingHom (scaleEquiv l hl).toRingHom) =
     algebraMap L E l•genericF d s a := by
 simp only [genericF,form,zWe,map_monomial,coe_mapRingHom,
   Finset.smul_sum,smul_monomial,smul_eq_mul]
 apply Finset.sum_congr rfl
 intro i _
 rw [show (scaleEquiv l hl).toRingHom (j (z9v (.inl i))) =
   scaleEquiv l hl (Lw (.inl i)) from rfl,slot_scaled]
 rfl
private theorem g_fixed (l:L) (hl:l≠0) :
  (genericG d s a).map (mapRingHom (scaleEquiv l hl).toRingHom)=genericG d s a := by
 simp only [genericG,form,zWe,map_monomial,coe_mapRingHom]
 apply Finset.sum_congr rfl
 intro i _
 rw [show (scaleEquiv l hl).toRingHom (j (z9v (.inr i))) =
  scaleEquiv l hl (Lw (.inr i)) from rfl,slot_scaled]
 simp [weight,Lw]
private theorem atPair_smul {F:Type} [Field F] (x y k :F) (f :F[X][X]) :
  atPair (zz4 F) x y (k•f)=k * atPair (zz4 F) x y f := by
 rw [show k•f=C (C k)*f from by
  rw [Algebra.smul_def,zG3 F F[X] F[X][X]]
  rfl]
 simp [atPair]
private theorem move_values (V:UniversalValue d s a b c) (l:L) (hl:l≠0) :
   ∃ τ:Fin V.size→Fin V.size,Function.Bijective τ ∧
     ∀ i,scaleEquiv l hl (pointValue V i)=algebraMap L E l*pointValue V (τ i) := by
 let σ:E ≃+* E :=scaleEquiv l hl
 let k :=algebraMap L E l
 have hk :k≠0:=(map_ne_zero_iff _ (algebraMap L E).injective).2 hl
 have hF:=f_scaled (d:=d) (s :=s) (a :=a) l hl
 have hG:=g_fixed (d:=d) (s :=s) (a :=a) l hl
 have next (i:Fin V.size) : ∃ n,V.pt n=(σ (V.pt i).1,σ (V.pt i).2) := by
   have hf :=atPair_hom σ.toRingHom (V.pt i).1 (V.pt i).2 (genericF d s a)
   have hg:=atPair_hom σ.toRingHom (V.pt i).1 (V.pt i).2 (genericG d s a)
   rw [V.f_zero,map_zero,show σ=scaleEquiv l hl from rfl,hF,atPair_smul] at hf
   rw [V.g_zero,map_zero,show σ=scaleEquiv l hl from rfl,hG] at hg
   exact V.all_roots _ _ ((mul_eq_zero.mp hf.symm).resolve_left hk) hg.symm
 let τ (i:Fin V.size) :=Classical.choose (next i)
 have hτ (i:Fin V.size) :V.pt (τ i)=(σ (V.pt i).1,σ (V.pt i).2) :=
   Classical.choose_spec (next i)
 refine ⟨τ,Finite.injective_iff_bijective.mp ?_,?_⟩
 · intro i n h
   have e :=(hτ i).symm.trans ((congrArg V.pt h).trans (hτ n))
   exact V.distinct (Prod.ext (σ.injective (congrArg Prod.fst e))
     (σ.injective (congrArg Prod.snd e)))
 · intro i
   have h:=atPair_hom σ.toRingHom (V.pt i).1 (V.pt i).2 (genericF d s a).derivative
   rw [← derivative_map,show σ=scaleEquiv l hl from rfl,hF,derivative_smul,
     atPair_smul] at h
   change σ (value b c (V.pt i))=k*value b c (V.pt (τ i))
   rw [hτ]
   simp only [value,qZu9hjc.gauge,map_div₀,map_pow,map_add,map_mul]
   change σ.toRingHom _/(σ (algebraMap L E b) +
     σ (algebraMap L E c)*σ (V.pt i).2)^(d-2)= _
   rw [show σ=scaleEquiv l hl from rfl,base_fixed,base_fixed,h,mul_div_assoc]
   rfl
private theorem aNz (r :D[X]) (t z :E) (f :D →+* E)
    (hc : ∀ x :L,f (znf x)=algebraMap L E x)
    (hx : ∀ i:Index d s a,f (z9v i)=Lw i+scaleSlope i*z) :
    (scaleLine r t).eval z=(r.map f).eval t:= by
  change ((evalRingHom z).comp (onLine (algebraMap L E) Lw scaleSlope t)) r =
    ((evalRingHom t).comp (mapRingHom f)) r
  apply zmU
  apply Polynomial.ringHom_ext
  · intro q
    simp only [zQb,coe_evalRingHom,onLine,coe_eval₂RingHom,
      eval₂_C,coe_mapRingHom,map_C,eval_C]
    change ((evalRingHom z).comp (zOD (C.comp (algebraMap L E))
      (fun i=>C (Lw i)+C (scaleSlope i)*z7y))) q=f q
    apply zmU
    apply zXT
    · intro x
      simpa only [zQb,zTv,coe_evalRingHom,eval_C]
        using (hc x).symm
    · intro i
      simpa only [zQb,zrD,coe_evalRingHom,eval_add,
        eval_mul,eval_C,eval_X] using (hx i).symm
  · simp [onLine]
private theorem d2N (r :D[X]) (t:E) (l:L) (hl:l≠0) :
   (scaleLine r t).eval (algebraMap L E l - 1) =
     ((r.map j).map (scaleEquiv l hl).toRingHom).eval t:= by
 rw [map_map]
 apply aNz
 · intro x
   exact base_fixed l hl x
 · intro i
   change scaleEquiv l hl (Lw i)= _
   rw [slot_scaled]
   cases i <;> simp only [scaleSlope,weight,map_one,one_mul,zero_mul,add_zero]
   ring
private theorem coeff_injective :zq4 (j:D →+* E) := by
 rw [IsScalarTower.algebraMap_eq D K₀ E]
 exact (algebraMap K₀ E).injective.comp (zxb D K₀)
private theorem scalar_eq (V:UniversalValue d s a b c) :
  j V.R.leadingCoeff=V.scalar := by
 have hm: (∏ i,(z7y - C (pointValue V i))).Monic :=
  monic_prod_of_monic _ _ (fun i _=>monic_X_sub_C _)
 have hp:=V.product
 change V.R.map j=C V.scalar * ∏ i,(z7y - C (pointValue V i)) at hp
 rw [← leadingCoeff_map_of_injective coeff_injective,hp,hm.leadingCoeff_C_mul]
private def factor {F:Type} [Field F] (t v :F) :F[X] :=
 C t - C v*(1+Polynomial.X)
private theorem line_factorization (V:UniversalValue d s a b c) (t:E) :
   scaleLine V.R t=scaleLine (C V.R.leadingCoeff) (0:E) *
     ∏ i,factor t (pointValue V i) := by
 classical
 apply eq_of_infinite_eval_eq
 let f (l:L) :=algebraMap L E l - 1
 have hf :zq4 f := fun _ _ h =>
   (algebraMap L E).injective (sub_left_inj.mp h)
 have hinf : (({0} : Set L)ᶜ).Infinite :=(Set.finite_singleton 0).infinite_compl
 refine (hinf.image hf.injOn).mono ?_
 rintro z ⟨l,hl,rfl⟩
 have hl' : l≠0:=hl
 obtain ⟨τ,hτ,hv⟩:=move_values V l hl'
 have hp:=V.product
 change V.R.map j=C V.scalar * ∏ i,(z7y - C (pointValue V i)) at hp
 change (scaleLine V.R t).eval (f l) =
   (scaleLine (C V.R.leadingCoeff) (0:E) * ∏ i,factor t (pointValue V i)).eval (f l)
 rw [d2N V.R t l hl',hp,eval_mul,d2N (C V.R.leadingCoeff) 0 l hl',
   map_C,map_C,eval_C,scalar_eq V]
 simp only [Polynomial.map_mul,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C,
   eval_mul,eval_C,eval_prod,eval_sub,eval_X,eval_add,eval_one,factor,f,
   add_sub_cancel]
 congr 1
 simp_rw [show ∀ x :E,(scaleEquiv l hl').toRingHom x=scaleEquiv l hl' x from fun _=>rfl,hv]
 simpa only [Function.comp_apply,mul_comm (algebraMap L E l)] using
   hτ.prod_comp (fun i=>t - algebraMap L E l*pointValue V i)
private theorem factor_order {F:Type} [Field F] {t v :F} (ht:t≠0) :
   factor t v≠0∧rootMultiplicity 0 (factor t v) =
    rootMultiplicity t (z7y - C v) := by
 by_cases h:v=t
 · subst v
   have hfac:factor t t=C (-t)*(z7y - C (0:F)) := by
    simp only [factor,map_neg,map_zero,sub_zero]
    ring
   have hn:=mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr ht)) (X_sub_C_ne_zero (0:F))
   rw [hfac,rootMultiplicity_mul hn,rootMultiplicity_C,zero_add,
    rootMultiplicity_X_sub_C_self,rootMultiplicity_X_sub_C_self]
   exact ⟨hn,rfl⟩
 · have he : (factor t v).eval 0≠0:= by
    simpa [factor] using sub_ne_zero.mpr (Ne.symm h)
   refine ⟨fun hz=>he (by simp [hz]),?_⟩
   rw [rootMultiplicity_eq_zero (fun hz=>he hz)]
   have hn : ¬ (z7y - C v).IsRoot t:= by
    simpa [IsRoot.def,sub_eq_zero,eq_comm] using h
   exact (rootMultiplicity_eq_zero hn).symm
private theorem prod_order {I F:Type} [Field F] (S:Finset I)
   (f g:I→F[X]) (x y :F) (hf : ∀ i,f i≠0) (hg : ∀ i,g i≠0)
   (h : ∀ i,rootMultiplicity x (f i)=rootMultiplicity y (g i)) :
   rootMultiplicity x (∏ i∈S,f i)=rootMultiplicity y (∏ i∈S,g i) := by
 classical
 induction S using Finset.induction_on with
 | empty=>simp only [Finset.prod_empty,← C_1,rootMultiplicity_C]
 | insert i S hi ih =>
   simp only [Finset.prod_insert hi]
   rw [rootMultiplicity_mul (mul_ne_zero (hf i) (Finset.prod_ne_zero_iff.mpr fun k _=>hf k)),
     rootMultiplicity_mul (mul_ne_zero (hg i) (Finset.prod_ne_zero_iff.mpr fun k _=>hg k)),h,ih]
theorem proof :q33Mraa.c2 := by
  classical
  intro d' s' a' b' c' V t ht
  let k :=algebraMap (jo d' s' a') (Generic d' s' a')
  let A:=scaleLine (C V.R.leadingCoeff) (0:Generic d' s' a')
  have hA:A.eval 0=V.scalar := by
    have he :=aNz (C V.R.leadingCoeff) 0 0 k
      (fun x=>(zG3 L (jo d' s' a') (Generic d' s' a') x).symm)
      (fun i=> by
        simp only [k,Lw,mul_zero,add_zero])
    rw [map_C,eval_C,scalar_eq V] at he
    exact he
  have hAn:A≠0:= fun h=>V.scalar_ne (by simpa [h] using hA.symm)
  have hv (i:Fin V.size) :=factor_order (v :=pointValue V i) ht
  have hleft:A * ∏ i,factor t (pointValue V i)≠0 :=
    mul_ne_zero hAn (Finset.prod_ne_zero_iff.mpr fun i _=>(hv i).1)
  have hright:C V.scalar * ∏ i,(z7y - C (pointValue V i))≠0 :=
    mul_ne_zero (C_ne_zero.mpr V.scalar_ne)
      (Finset.prod_ne_zero_iff.mpr fun i _=>X_sub_C_ne_zero _)
  have hp:=V.product
  change V.R.map k=C V.scalar * ∏ i,(z7y - C (pointValue V i)) at hp
  rw [line_factorization V,hp]
  change (A * ∏ i,factor t (pointValue V i))≠0 ∧
    rootMultiplicity 0 (A * ∏ i,factor t (pointValue V i)) =
      rootMultiplicity t (C V.scalar * ∏ i,(z7y - C (pointValue V i)))
  refine ⟨hleft,?_⟩
  rw [rootMultiplicity_mul hleft,rootMultiplicity_mul hright,rootMultiplicity_C,
    rootMultiplicity_eq_zero (p:=A) (x :=0) (fun h=>V.scalar_ne (hA.symm.trans h)),
    zero_add,zero_add]
  exact prod_order _ _ _ _ _ (fun i=>(hv i).1) (fun i=>X_sub_C_ne_zero _) (fun i=>(hv i).2)
end
end q8hd3Fb
end
end
section
section
namespace qSHe4ub
open P5 (p)
open qPY5jQe (degree threshold)
def c1 :Prop :=qZV9OWb.c1
def c2 :Prop :=qZV9OWb.c2
def c3:Prop :=qZV9OWb.c3
def c4 :Prop :=qZV9OWb.c4
def c5:Prop :=qZV9OWb.c5
private theorem guards {e :ℕ} (he :e≤13) :
  e<p∧e*degree≤threshold∧(2*e-1)*threshold-e^2*degree<p:= by
 have h: (2*e-1)*threshold≤25*threshold :=ztf _ (by omega)
 exact ⟨he.trans_lt (by decide),(Nat.mul_le_mul_right degree he).trans (by decide),
  ((Nat.sub_le ..).trans h).trans_lt (by decide)⟩
theorem of_children (bY:c1) (Oj:c2) (exL:c3)
  (qW:c4) (QI:c5) :qPY5jQe.c3:= by
 intro q C z s F e hd hde he hw hs
 obtain ⟨hp,hW,hpolar⟩:=guards he
 exact qZV9OWb.of_children bY Oj exL qW QI
  F degree e threshold (by decide) hd hde hp hW hpolar hw hs
end qSHe4ub
end
section
set_option backward.isDefEq.respectTransparency false
namespace qOdV5gc
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L FX j9)
open P5_7_7 (phys)
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel cLN specialize)
open q1kuFjb (principal reduced_pair)
open P5_7_3_5_2 (Sheet Variation atPolynomial)
open qrezXJe (resultant_val_le sheet_bound sum_zeroOrder)
open qgbTAnb (slice extract coeff_extract degree_extract liftSeries degree_lift map_lift
 fWX linear_root fraction_degrees padded_ne padded_order)
open E7 (KB)
open private expansion_linear from ProximityPrize.SubmissionLower.Z4uF8Nb
open private primitive_pair from ProximityPrize.SubmissionLower.ZhlCjsa
variable {q:Curve} {Cq:CurveModel q} {z :K→K} {s :K→K[X]}
private theorem slice_ne {E :Type} [Field E] [Algebra L E] (φ:E →ₐ[L] LaurentSeries L)
  {b:E[X]} (hb:b.Monic) :slice φ 0 b≠0:= by
 intro hz
 have h:=coeff_extract (u:= fun c=>(φ c).coeff 0) (by simp) b b.natDegree
 rw [show (extract (fun c=>(φ c).coeff 0) b)=slice φ 0 b from rfl,hz,
  coeff_zero,hb.coeff_natDegree,map_one] at h
 simp [HahnSeries.coeff_one] at h
private theorem monic_leading (F:Sheet Cq z s) (hd:F.d = 1) : (F.f.coeff 1).Monic:= by
 change (F.f.coeff 1).leadingCoeff=1
 simpa only [hd] using F.normalized
private theorem local_variation (F:Sheet Cq z s) (hd:F.d = 1)
    {γ:K} (hγ:γ∈F.marks) (D M:ℕ)
    (hb: (F.f.coeff 1).natDegree≤M) (ha : (F.f.coeff 0).natDegree≤M+D)
    (hs : (s γ).natDegree≤D) :
    let φ:=F.atPlace γ hγ
    ∃ u v :L[X],v≠0∧IsCoprime u v ∧
      atPolynomial (cLN φ 0 F.f).derivative (s γ)≠0 ∧
      phys u/phys v =
        -(atPolynomial (cLN φ 1 F.f) (s γ) /
          atPolynomial (cLN φ 0 F.f).derivative (s γ)) ∧
      max v.natDegree (u.natDegree-D)≤M:= by
  dsimp only
  let φ:=F.atPlace γ hγ
  let b:=F.f.coeff 1
  let a :=F.f.coeff 0
  let P:=j9 (s γ)
  let n := -(slice φ 1 b*P+slice φ 1 a)
  let d:=slice φ 0 b
  have hm:b.Monic:=monic_leading F hd
  have hne :d≠0:=slice_ne φ hm
  have hden:atPolynomial (cLN φ 0 F.f).derivative (s γ)=phys d:= by
    rw [expansion_linear φ 0 hd.le,derivative_add,derivative_C_mul_X,derivative_C,add_zero]
    exact eval₂_C _ _
  let t := -(atPolynomial (cLN φ 1 F.f) (s γ) /
    atPolynomial (cLN φ 0 F.f).derivative (s γ))
  have ht:t=phys n/phys d:= by
    change -(atPolynomial _ _/atPolynomial _ _)= _
    rw [hden,expansion_linear φ 1 hd.le]
    simp only [atPolynomial,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,n,b,a,P,
      map_neg,map_mul,map_add,neg_div]
  obtain ⟨u,v,hv,hcop,huv⟩:=reduced_pair t
  obtain ⟨hv',hu'⟩:=fraction_degrees hv hne hcop (huv.trans ht)
  have hn:n.natDegree≤M+D:= by
    have hP:P.natDegree≤D:=natDegree_map_le.trans hs
    rw [show n = -(slice φ 1 b*P+slice φ 1 a) from rfl,natDegree_neg]
    exact (natDegree_add_le _ _).trans (max_le
      (natDegree_mul_le.trans (Nat.add_le_add ((degree_extract (by simp) b).trans hb) hP))
      ((degree_extract (by simp) a).trans ha))
  refine ⟨u,v,hv,hcop,?_,huv,max_le (hv'.trans ((degree_extract (by simp) b).trans hb)) (by omega)⟩
  rw [hden]
  exact (map_ne_zero_iff _ (zxb L[X] FX)).mpr hne
private theorem mark_order (F:Sheet Cq z s) (hd:F.d = 1)
   {γ:K} (hγ:γ∈F.marks) (D M:ℕ)
   (hb: (F.f.coeff 1).natDegree≤M) (ha : (F.f.coeff 0).natDegree≤M+D)
   (hs : (s γ).natDegree≤D)
   (hr : (F.f.coeff 1).resultant (F.f.coeff 0) M (M+D)≠0) :
   M≤KB (F.place γ).value ((F.f.coeff 1).resultant (F.f.coeff 0) M (M+D)) := by
 let φ:=F.atPlace γ hγ
 let b:=F.f.coeff 1
 let a :=F.f.coeff 0
 let b₀:=slice φ 0 b
 let a₀:=slice φ 0 a
 let P:=j9 (s γ)
 let B:=liftSeries φ b
 let A:=liftSeries φ a
 let k :=M-b₀.natDegree
 have hb₀:b₀≠0:=slice_ne φ (monic_leading F hd)
 have hP:P.natDegree≤D:=natDegree_map_le.trans hs
 have hz :specialize (cLN φ 0 F.f) P 1=0:= by
   simpa only [specialize,atPolynomial,P,map_one,div_one] using F.root γ hγ
 have hroot :b₀*P+a₀=0:= by
   simpa only [mul_one] using linear_root φ hd.le one_ne_zero hz
 have he :a₀ = -(b₀*P) :=eq_neg_of_add_eq_zero_right hroot
 have hM:b₀.natDegree≤M:=(degree_extract (by simp) b).trans hb
 have hB:B.map zbO=b₀:=fWX φ b
 have hA:A.map zbO=a₀:=fWX φ a
 have hk :k≤M:=Nat.sub_le _ _
 have hEq:b₀.natDegree+k=M:=Nat.add_sub_of_le hM
 have hMa :a₀.natDegree≤M+D-k := by
   rw [he,natDegree_neg]
   exact natDegree_mul_le.trans (by omega)
 let G:=normalize b₀
 have hG:G.natDegree=b₀.natDegree :=natDegree_normalize
 have hdiv :=padded_order B A ((degree_lift φ b).trans hb) ((degree_lift φ a).trans ha)
   hk (hk.trans (Nat.le_add_right _ _)) (monic_normalize hb₀) (by change G.natDegree≤_; omega)
   (by rw [hB]; exact normalize_dvd_iff.mpr dvd_rfl)
   (by rw [hA,he]; exact dvd_neg.mpr (normalize_dvd_iff.mpr (dvd_mul_right b₀ P)))
   (by rw [hB]; omega) (by rwa [hA])
 rw [show (normalize b₀).natDegree=b₀.natDegree from hG,hEq] at hdiv
 let R:=b.resultant a M (M+D)
 let T:=B.resultant A M (M+D)
 have hT:algebraMap (PowerSeries L) (LaurentSeries L) T=φ R:= by
   rw [show T= _ from rfl,← resultant_map_map,
     map_lift φ b (fun i=>(F.value γ hγ _).symm.trans_le (F.integral γ hγ 1 i)),
     map_lift φ a (fun i=>(F.value γ hγ _).symm.trans_le (F.integral γ hγ 0 i)),
     resultant_map_map]
   rfl
 have hv : (F.place γ).value R≤WithZero.exp (-(M:ℤ)) := by
   rw [F.value γ hγ,← hT]
   exact (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero L T).mpr
     (PowerSeries.X_pow_dvd_iff.mp hdiv)
 have hR:R≠0:=hr
 have hlog:WithZero.log ((F.place γ).value R) ≤ -(M:ℤ) :=
   (WithZero.log_le_iff_le_exp ((F.place γ).value.ne_zero_iff.mpr hR)).mpr hv
 change M≤(-WithZero.log ((F.place γ).value R)).toNat
 omega
theorem proof :qXmh4Jb.c4 := by
  intro q Cq z s F D W _ hDW hd hW hs
  let b:=F.f.coeff 1
  let a :=F.f.coeff 0
  let M:=max b.natDegree (a.natDegree-D)
  have hmon :b.Monic:=monic_leading F hd
  have hb:b.natDegree≤M:=le_max_left _ _
  have ha :a.natDegree≤M+D:= by have :=le_max_right b.natDegree (a.natDegree-D); omega
  have hbW:b.natDegree+D ≤W:= by simpa [b] using hW 1 hmon.ne_zero
  have haW:a.natDegree≤W:= by
    by_cases h:a=0
    · simp [h]
    · simpa [a] using hW 0 h
  have hMW:M≤W-D:=max_le (by omega) (zIu haW D)
  have ht:b.natDegree=M∨a.natDegree=M+D ∧a≠0:= by
    by_cases h:b.natDegree=M
    · exact Or.inl h
    · right
      have hne :a≠0:= by
        intro hz
        apply h
        simp [M,hz]
      dsimp [M] at h ⊢
      exact ⟨by omega,hne⟩
  let R:=b.resultant a M (M+D)
  have hR:R≠0:=padded_ne hmon.ne_zero (primitive_pair F.irreducible hd) hb ha ht
  have hbudget : ∑ γ∈F.marks,KB (F.place γ).value R≤(M+(M+D))*F.h:= by
    apply sum_zeroOrder (principal Cq) F.marks F.place F.distinct F.f R _ hR
    intro w
    have h:=sheet_bound w.value F.f
    exact (resultant_val_le w.value b a M (M+D) _ (h 1) (h 0)).trans_eq
      (by rw [← WithZero.exp_nsmul]; simp)
  have hex (γ:K) : ∃ u v :L[X],∀ hγ:γ∈F.marks,
      v≠0∧IsCoprime u v ∧
      atPolynomial (cLN (F.atPlace γ hγ) 0 F.f).derivative (s γ)≠0 ∧
      phys u/phys v = -(atPolynomial (cLN (F.atPlace γ hγ) 1 F.f) (s γ) /
        atPolynomial (cLN (F.atPlace γ hγ) 0 F.f).derivative (s γ)) ∧
      max v.natDegree (u.natDegree-D)≤M:= by
    by_cases hγ:γ∈F.marks
    · obtain ⟨u,v,huv⟩:=local_variation F hd hγ D M hb ha (hs γ hγ)
      exact ⟨u,v,fun _=>huv⟩
    · exact ⟨0,1,fun h=>(hγ h).elim⟩
  choose u v hv using hex
  let V:Variation F:=⟨F.marks,fun _ h=>h,u,v,fun γ h=>(hv γ h).1,
    fun γ h=>(hv γ h).2.1,fun γ h=>(hv γ h).2.2.1,fun γ h=>(hv γ h).2.2.2.1⟩
  refine ⟨V,by simp [V],?_⟩
  calc
    _ ≤ ∑ γ∈F.marks,KB (F.place γ).value R:=sum_le_sum fun γ hγ =>
      ((hv γ hγ).2.2.2.2).trans (mark_order F hd hγ D M hb ha (hs γ hγ) hR)
    _≤(M+(M+D))*F.h:=hbudget
    _≤_:=ztf _ (by omega)
end
end qOdV5gc
end
section
set_option autoImplicit true
namespace qXKgtFd
theorem proof :qPY5jQe.c4 := by
 intro q C z s F hd hw hs
 exact qOdV5gc.proof F qPY5jQe.degree qPY5jQe.threshold
  (by decide) (by decide) hd hw hs
end qXKgtFd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qvghFhc
noncomputable section
open Polynomial
open scoped Classical WithZero
open cu (L)
open E7 (KB)
open qrezXJe (residuePoly discriminantResultant)
open qgbTAnb (liftSeries degree_lift map_lift fWX padded_ne padded_order)
open private residue_nonzero from ProximityPrize.SubmissionLower.ZfSxMva
theorem proof :qrezXJe.c2 := by
  intro E _ _ G w a ha hs _ hI hu
  let F:=residuePoly a G
  let H :=liftSeries a G
  let m:=G.natDegree
  let n:=m-1
  let d:=EuclideanDomain.gcd F F.derivative
  have hF:F≠0:=residue_nonzero G w a ha hu
  have hd:d≠0:= fun h=>hF (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hdF:d∣F:=EuclideanDomain.gcd_dvd_left _ _
  have hdF' : d∣F.derivative :=EuclideanDomain.gcd_dvd_right _ _
  have hH :H.map zbO=F:=fWX a G
  have hH' : H.derivative.map zbO=F.derivative := by
    rw [← derivative_map,hH]
  have hm:H.natDegree≤ m:=degree_lift a G
  have hn:H.derivative.natDegree≤n :=
    (natDegree_derivative_le H).trans (zIu hm 1)
  have hFm:F.natDegree≤ m:=hH ▸ natDegree_map_le.trans hm
  have hab:d.natDegree≤ m+n :=
    (natDegree_le_of_dvd hdF hF).trans (hFm.trans (Nat.le_add_right m n))
  have hdiv :PowerSeries.X^d.natDegree∣H.resultant H.derivative m n:= by
    simpa only [natDegree_normalize,Nat.add_zero] using
      padded_order H H.derivative hm hn (k :=0) (Nat.zero_le _) (Nat.zero_le _) (D:=normalize d)
        (monic_normalize hd) (by simpa only [natDegree_normalize,zPv] using hab)
        (hH.symm ▸ normalize_dvd_iff.mpr hdF)
        (hH'.symm ▸ normalize_dvd_iff.mpr hdF')
        (by simpa only [zPv] using natDegree_map_le.trans hm)
        (by simpa only [zPv] using natDegree_map_le.trans hn)
  let b:=algebraMap (PowerSeries L) (LaurentSeries L)
  have hmap :H.map b=G.map a.toRingHom :=
    map_lift a G fun i=> by simpa [← ha] using hI i
  have hres :b (H.resultant H.derivative m n)=a (discriminantResultant G) := by
    rw [← resultant_map_map,← derivative_map,hmap,derivative_map,resultant_map_map]
    rfl
  have hv :w.value (discriminantResultant G)≤WithZero.exp (-(d.natDegree :ℤ)) := by
    rw [ha,← hres]
    exact (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero L _).mpr
      (PowerSeries.X_pow_dvd_iff.mp hdiv)
  have hne :discriminantResultant G≠0 :=
    padded_ne hs.ne_zero hs le_rfl (natDegree_derivative_le G) (.inl rfl)
  have hl:=(WithZero.log_le_iff_le_exp (w.value.zero_iff.not.mpr hne)).mpr hv
  simpa [KB,d,F] using Int.toNat_le_toNat (neg_le_neg hl)
end
end qvghFhc
end
end
