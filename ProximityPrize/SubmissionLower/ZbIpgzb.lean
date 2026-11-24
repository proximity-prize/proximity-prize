import ProximityPrize.SubmissionLower.Zk6yNvb
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, MvPolynomial → z3y, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.coeToPowerSeries.ringHom_apply → zwl, Polynomial.map_zero → zgY, Polynomial.ringHom_ext → z86, PowerSeries.constantCoeff → zbO, RingHom.comp_apply → zQb, RingHom.id → zz4
set_option autoImplicit true
section
namespace qFQL0Vc
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil relativePolar bix)
open qfbIfsd (Slot Index baseCap ordCap const₂ gaugeForm actual form)
abbrev Closure (E :Type) [Field E] :=AlgebraicClosure (RatFunc E)
abbrev Series (E :Type) [Field E] :=PowerSeries (Closure E)
variable {E :Type} [Field E]
def parameter :E[X] →+* Closure E :=
 (algebraMap (RatFunc E) (Closure E)).comp (algebraMap E[X] (RatFunc E))
variable [Algebra L E] {A:Equation E}
abbrev Direction (A:Equation E) :=Index A→L
def constants :L →+* Closure E :=parameter.comp (Polynomial.C.comp (algebraMap L E))
def alpha (C:Pencil A) (r :Index A) :Closure E :=parameter ((actual C r).coeff 0)
def beta (C:Pencil A) (r :Index A) :Closure E :=parameter ((actual C r).coeff 1)
theorem beta_polar (C:Pencil A) (u:Slot A.s (baseCap A 2) (ordCap A 2)) :
  beta C ⟨2,u⟩ = -constants (if u.2.val=0 then (gaugeForm C.tilt A.d).coeff u.1 else 0) := by
 simp [beta,actual,constants,const₂]
def D6 (a :Index A→Closure E) (k :Fin 3) (x y :Closure E) :Closure E :=
  ∑ u:Slot A.s (baseCap A k) (ordCap A k),
    a ⟨k,u⟩*(u.2.val :Closure E)*x^(u.2.val-1)*y ^u.1.val
def partialY (a :Index A→Closure E) (k :Fin 3) (x y :Closure E) :Closure E :=
  ∑ u:Slot A.s (baseCap A k) (ordCap A k),
    a ⟨k,u⟩*(u.1.val :Closure E)*x^u.2.val*y ^(u.1.val-1)
def jacobian (a :Index A→Closure E) (x y :Closure E) :Closure E :=
 D6 a 0 x y*partialY a 1 x y - partialY a 0 x y*D6 a 1 x y
structure Fiber (C:Pencil A) where
 size :ℕ
 x :Fin size→Closure E
 y :Fin size→Closure E
 f_zero : ∀ i,form (alpha C) 0 (x i) (y i)=0
 g_zero : ∀ i,form (alpha C) 1 (x i) (y i)=0
 simple : ∀ i,jacobian (alpha C) (x i) (y i)≠0
 scale_ne : ∀ i,form (beta C) 2 (x i) (y i)≠0
 separates : ∀ i j,i≠j → ∃ u:Slot A.s (baseCap A 2) (ordCap A 2),
   x i^u.2.val*y i^u.1.val/form (beta C) 2 (x i) (y i) ≠
     x j^u.2.val*y j^u.1.val/form (beta C) 2 (x j) (y j)
 product : (bix C.base (relativePolar C) C.finite).map
     (algebraMap (RatFunc E) (Closure E)) =
   ∏ i,(z7y-Polynomial.C
     (-(form (alpha C) 2 (x i) (y i))/form (beta C) 2 (x i) (y i)))
def ic (C:Pencil A) (z :Direction A) (r :Index A) :Series E :=
 PowerSeries.C (alpha C r)+PowerSeries.C (constants (z r))*PowerSeries.X
def sample (C:Pencil A) (R:z3y (Index A) L) (z :Direction A) :Closure E :=
 R.eval₂ constants (fun r=>alpha C r+constants (z r))
structure Lift {C:Pencil A} (B:Fiber C) (z :Direction A) where
 x :Fin B.size→Series E
 y :Fin B.size→Series E
 x₀ : ∀ i,zbO (x i)=B.x i
 y₀ : ∀ i,zbO (y i)=B.y i
 f_zero : ∀ i,form (ic C z) 0 (x i) (y i)=0
 g_zero : ∀ i,form (ic C z) 1 (x i) (y i)=0
def scale {C:Pencil A} {B:Fiber C} {z :Direction A} (U:Lift B z)
    (i:Fin B.size) :Series E :=
  form (PowerSeries.C ∘ beta C) 2 (U.x i) (U.y i)
def value {C:Pencil A} {B:Fiber C} {z :Direction A} (U:Lift B z)
    (z' : Direction A) (i:Fin B.size) :Series E :=
  -(form (ic C z') 2 (U.x i) (U.y i))*(scale U i)⁻¹
end
end qFQL0Vc
end
section
open PowerSeries renaming C→qz0,constantCoeff→qz1,coeff_zero_eq_constantCoeff_apply→qz4
open Polynomial renaming mapRingHom→qz2
open IsFractionRing renaming injective→qz3
open MvPolynomial renaming eval₂_comp_left→qz5
set_option backward.isDefEq.respectTransparency false
namespace qFQL0Vc
noncomputable section
open Polynomial Finset
open scoped Classical
open cu (L)
open bay (aER)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil)
open qfbIfsd (Index actual const₂ form deform deformArg Detects)
variable {E :Type} [Field E]
private def a5j :E[X][X] →+* (Series E)[X] :=
 qz2 (qz0.comp parameter)
def convert:E[X][X][X] →+* (Series E)[X] :=
 eval₂RingHom a5j (z1z PowerSeries.X)
private theorem swap_convert (P:E[X][X][X]) :
    aER (zz4 (Series E)) (convert P) =
      Polynomial.coeToPowerSeries.ringHom
        (P.map (qz2 (parameter (E :=E)))) := by
  change ((aER (zz4 (Series E))).comp convert) P =
    (Polynomial.coeToPowerSeries.ringHom.comp
      (qz2 (qz2 (parameter (E :=E))))) P
  congr 1
  apply z86
  · intro p
    simp only [zQb,convert,coe_eval₂RingHom,eval₂_C,Polynomial.coe_mapRingHom,map_C,
      zwl,Polynomial.coe_C]
    change ((aER (zz4 (Series E))).comp a5j) p =
      (qz0.comp (qz2 (parameter (E :=E)))) p
    congr 1
    apply z86
    · intro a
      simp [a5j]
    · simp [a5j]
  · simp [convert]
private theorem coeff_swap (P:E[X][X][X]) (n:ℕ) :
   PowerSeries.coeff n (aER (zz4 (Series E)) (convert P)) =
     (P.coeff n).map (parameter (E :=E)) := by
 rw [swap_convert,zwl,Polynomial.coeff_coe,
   coeff_map]
 rfl
private theorem linear_product {S:Type} [CommRing S] [IsDomain S]
  {ι:Type} [Fintype ι] (t:ι→S) (ht:zq4 t) (D:S[X])
  (hroot : ∀ i,D.eval (t i)=0) :
  (∏ i,((z7y:S[X]) - C (t i)))∣D:= by
 let j:=algebraMap S (FractionRing S)
 have hj:=qz3 S (FractionRing S)
 rw [← map_dvd_map j hj (monic_prod_of_monic _ _ fun i _=>monic_X_sub_C (t i)),
  Polynomial.map_prod]
 simp only [Polynomial.map_sub,map_X,map_C]
 apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C (hj.comp ht))
 intro i
 rw [dvd_iff_isRoot,IsRoot]
 change (D.map j).eval (j (t i))=0
 rw [eval_map_apply,hroot,map_zero]
theorem extract_dvd (P:E[X][X][X]) (hP:P≠0)
    {ι:Type} [Fintype ι] (t:ι→Series E) (ht:zq4 t)
    (hroot : ∀ i,(convert P).eval (t i)=0) (N : (RatFunc E)[X]) (hN :N.Monic)
    (hprod:N.map (algebraMap (RatFunc E) (Closure E)) =
      ∏ i,(z7y - C (qz1 (t i)))) :
    ∃ n,P.coeff n≠0∧N∣(P.coeff n).map (algebraMap E[X] (RatFunc E)) := by
  let V := ∏ i,((z7y: (Series E)[X]) - C (t i))
  obtain ⟨G,hG⟩:=linear_product t ht (convert P) hroot
  let q0:=aER (zz4 (Series E))
  have hV:qz1 (q0 V)=N.map (algebraMap (RatFunc E) (Closure E)) := by
    rw [hprod]
    simp [V,q0,← qz4,
      -PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map]
  have hGne :q0 G≠0:= by
    intro hz
    have hd:q0 (convert P)=0:= by rw [hG,map_mul,hz,mul_zero]
    apply hP
    apply Polynomial.ext
    intro n
    rw [coeff_zero]
    apply Polynomial.map_injective parameter
      ((algebraMap (RatFunc E) (Closure E)).injective.comp (qz3 E[X] (RatFunc E)))
    rw [zgY,← coeff_swap,show aER _ _ = _ from hd,map_zero]
  let n:=(q0 G).order.toNat
  have q1 :
      (P.coeff n).map parameter =
        N.map (algebraMap (RatFunc E) (Closure E)) *
          qz1 (PowerSeries.divXPowOrder (q0 G)) := by
    rw [← coeff_swap,show aER (zz4 (Series E)) _=q0 (V*G) from
      congrArg q0 hG,map_mul]
    conv_lhs=>rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f :=q0 G),mul_left_comm]
    simpa only [zero_add,qz4,map_mul,hV] using
      PowerSeries.coeff_X_pow_mul (q0 V*PowerSeries.divXPowOrder (q0 G)) n 0
  refine ⟨n,?_,?_⟩
  · intro hz
    rw [hz,zgY] at q1
    exact (mul_ne_zero (hN.map _).ne_zero
      (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hGne)) q1.symm
  · apply (map_dvd_map _ (algebraMap (RatFunc E) (Closure E)).injective hN).mp
    rw [Polynomial.map_map]
    exact ⟨_,q1⟩
variable [Algebra L E] {A:Equation E}
theorem exists_sample (C:Pencil A) {R:z3y (Index A) L} (hR:R≠0) :
  ∃ z,sample C R z≠0:= by
 by_contra! h
 let j:=constants (E :=E)
 let S (r :Index A) :=Set.range (fun a :L=>alpha C r+j a)
 have hS (r :Index A) : (S r).Infinite :=Set.infinite_range_of_injective fun a b hab =>
  j.injective (add_left_cancel hab)
 apply hR
 apply (MvPolynomial.map_injective _ j.injective)
 rw [map_zero]
 apply MvPolynomial.funext_set S hS
 intro x hx
 choose z hz using fun r=>hx r (Set.mem_univ r)
 have he :x=fun r=>alpha C r+j (z r) :=funext fun r=>(hz r).symm
 rw [he,MvPolynomial.eval_map]
 exact h z
private theorem actual_affine (C:Pencil A) (r :Index A) :
  actual C r=z1z ((actual C r).coeff 0) +
   z1z ((actual C r).coeff 1)*Polynomial.X:= by
 rcases r with ⟨k,⟨i,j⟩⟩
 fin_cases k <;> simp [actual,const₂,sub_eq_add_neg]
 ring
theorem beta_zero (C:Pencil A) (r :Index A) (hr :r.1≠2) :beta C r=0:= by
 rcases r with ⟨k,⟨i,j⟩⟩
 fin_cases k <;> simp_all [beta,actual,const₂,coeff_sub]
private theorem eval_convert (C:Pencil A) (z :Direction A) (R:z3y (Index A) L)
    (t:Series E) :
    (convert (deform R (actual C) z)).eval t =
      R.eval₂ (qz0.comp constants)
        (fun r=>ic C z r+qz0 (beta C r)*t) := by
  let ev :=(evalRingHom t).comp (convert (E :=E))
  change ev (deform R (actual C) z)= _
  rw [deform,qz5 (S₁:=E[X][X][X]) (S₂:=Series E) ev]
  have hc:ev.comp (Polynomial.C.comp (const₂.comp (algebraMap L E))) =
      qz0.comp constants := by
    apply RingHom.ext
    intro a
    simp [ev,convert,a5j,const₂,constants]
  have hv :ev ∘ (fun r=>deformArg (actual C r) (z r)) =
      fun r=>ic C z r+qz0 (beta C r)*t:= by
    funext r
    simp only [Function.comp_apply,deformArg,map_add,map_mul]
    rw [show ev (z1z (const₂ (algebraMap L E (z r)))) =
      qz0 (constants (z r)) from RingHom.congr_fun hc (z r)]
    have hX:ev z7y=PowerSeries.X:= by simp [ev,convert]
    have h:ev (z1z (actual C r)) =
        qz0 (alpha C r)+qz0 (beta C r)*t:= by
      simp only [ev,zQb,convert,coe_eval₂RingHom,eval₂_C,coe_evalRingHom]
      nth_rw 1 [actual_affine C r]
      simp [a5j,alpha,beta]
    rw [hX,h,ic]
    abel
  rw [hc,hv]
theorem deform_ne (C:Pencil A) (R:z3y (Index A) L) (z :Direction A)
    (hz :sample C R z≠0) :deform R (actual C) z≠0:= by
  let ev :=(evalRingHom (0:Closure E)).comp
    ((evalRingHom (1 : (Closure E)[X])).comp
      (qz2 (qz2 (parameter (E :=E)))))
  have hs :ev (deform R (actual C) z)=sample C R z := by
    rw [deform,qz5 (S₁:=E[X][X][X]) (S₂:=Closure E) ev,sample]
    have hc:ev.comp (Polynomial.C.comp (const₂.comp (algebraMap L E)))=constants := by
      ext a
      simp [ev,const₂,constants,parameter]
    have hv :ev ∘ (fun r=>deformArg (actual C r) (z r)) =
        fun r=>alpha C r+constants (z r) := by
      funext r
      simp [ev,deformArg,alpha,constants,const₂,← coeff_zero_eq_eval_zero]
    rw [hc,hv]
  exact fun h=>hz (by rw [← hs,h,map_zero])
omit [Algebra L E] in
theorem map_form {M N :Type} [CommSemiring M] [CommSemiring N] (j:M →+* N)
 (a :Index A→M) (k :Fin 3) (x y :M) :
 j (form a k x y)=form (j ∘ a) k (j x) (j y) := by simp [form]
omit [Algebra L E] in
private theorem form_affine {M:Type} [CommRing M] (a b:Index A→M)
  (k :Fin 3) (x y t:M) :
  form (fun r=>a r+b r*t) k x y=form a k x y+form b k x y*t:= by
 simp only [form,Finset.sum_mul,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro i _
 ring
theorem scale₀ {C:Pencil A} {B:Fiber C} {z :Direction A} (U:Lift B z) (i:Fin B.size) :
  qz1 (scale U i)=form (beta C) 2 (B.x i) (B.y i) := by
 simp [scale,form,U.x₀,U.y₀]
theorem value₀ {C:Pencil A} {B:Fiber C} {z :Direction A} (U:Lift B z)
   (z' : Direction A) (i:Fin B.size) :
   qz1 (value U z' i) =
     -(form (alpha C) 2 (B.x i) (B.y i))/form (beta C) 2 (B.x i) (B.y i) := by
 rw [value,map_mul,PowerSeries.constantCoeff_inv,scale₀,map_neg,div_eq_mul_inv]
 congr 2
 rw [map_form,U.x₀,U.y₀]
 simp [ic,Function.comp_def]
theorem value_root {C:Pencil A} {B:Fiber C} {z :Direction A} (U:Lift B z)
   (z' : Direction A) (h : ∀ r,r.1≠2→z' r=z r)
   (R:z3y (Index A) L) (hR:Detects R) (i:Fin B.size) :
   (convert (deform R (actual C) z')).eval (value U z' i)=0:= by
 rw [eval_convert]
 let j:=algebraMap (Series E) (FractionRing (Series E))
 let a (r :Index A) :=ic C z' r+qz0 (beta C r)*value U z' i
 change R.eval₂ (qz0.comp constants) a=0
 apply qz3 (Series E) (FractionRing (Series E))
 rw [map_zero,qz5 j]
 apply hR _ _ (j (U.x i)) (j (U.y i))
 intro k
 rw [← map_form,map_eq_zero_iff _ (qz3 (Series E) (FractionRing (Series E)))]
 have hz (k :Fin 3) (hk :k≠2) :
     form a k (U.x i) (U.y i)=form (ic C z) k (U.x i) (U.y i) := by
   unfold form
   apply Finset.sum_congr rfl
   intro r _
   simp [a,ic,beta_zero C ⟨k,r⟩ hk,h ⟨k,r⟩ hk]
 fin_cases k
 · exact (hz 0 (by decide)).trans (U.f_zero i)
 · exact (hz 1 (by decide)).trans (U.g_zero i)
 · change form a 2 (U.x i) (U.y i)=0
   rw [show form a 2 _ _ = _ from
     form_affine (ic C z') (qz0 ∘ beta C) 2 _ _ _]
   change _+scale U i*value U z' i=0
   have hs :qz1 (scale U i)≠0:=(scale₀ U i).symm ▸ B.scale_ne i
   let p:=form (ic C z') 2 (U.x i) (U.y i)
   change p+scale U i*(-p*(scale U i)⁻¹)=0
   calc
     _=p - p*(scale U i*(scale U i)⁻¹) := by ring
     _=0:= by rw [PowerSeries.mul_inv_cancel _ hs,mul_one,sub_self]
end
end qFQL0Vc
end
