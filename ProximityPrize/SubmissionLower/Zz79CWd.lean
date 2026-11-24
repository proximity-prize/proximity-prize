import ProximityPrize.SubmissionLower.ZpFWnLb
import ProximityPrize.SubmissionLower.ZKzStyc
import ProximityPrize.SubmissionLower.Z4ocXpc
import ProximityPrize.SubmissionLower.Zk6yNvb
import ProximityPrize.SubmissionLower.P5_7_1_7_4_3_4_2Split
import ProximityPrize.SubmissionLower.Z877yta
import ProximityPrize.SubmissionLower.P5_7_1_7_4_3_4Split
import ProximityPrize.SubmissionLower.ZiH02Bd
import ProximityPrize.SubmissionLower.Zhgm4se
import ProximityPrize.SubmissionLower.ZTeGCOe
import ProximityPrize.SubmissionLower.Z9w0Rrc
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.lmul → zXA, CommRing → za6, Field → zrb, Fin.sum_univ_eq_sum_range → zdx, Finset.sum_congr → zUo, Finset.sum_mul → zkq, Finset.sum_sub_distrib → zQq, Fintype.sum_sigma → zla, Function.comp_apply → z3s, Int.toNat_le_toNat → z0Z, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Polynomial.X → z7y, Polynomial.hom_eval₂ → zly, Polynomial.map_sum → zWe, PowerSeries.constantCoeff → zbO, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
section
set_option autoImplicit true
namespace P5_7_1_7_4_3_4_2_2_2
noncomputable section
open Polynomial
open qfzuawb (map₂)
open qNu3xvc (Equation)
open qfbIfsd (Slot Vars Index form)
open qFQL0Vc (Closure Series alpha ic D6 partialY jacobian)
open private lift ev px py from ProximityPrize.SubmissionLower.ZKzStyc
private def block {R:Type} [za6 R] {s :ℕ} {b e :Fin 3→ℕ}
    (a :Vars s b e→R) (k :Fin 3) :R[X][X] :=
  ∑ u:Slot s (b k) (e k),monomial u.1.val (monomial u.2.val (a ⟨k,u⟩))
private theorem map_block {R S:Type} [za6 R] [za6 S] {s :ℕ} {b e :Fin 3→ℕ}
    (j:R →+* S) (a :Vars s b e→R) (k :Fin 3) :
    map₂ j (block a k)=block (j ∘ a) k := by
  simp only [block,map₂,coe_mapRingHom,zWe,map_monomial,z3s]
private theorem eval_block {R:Type} [za6 R] {s :ℕ} {b e :Fin 3→ℕ}
    (a :Vars s b e→R) (k :Fin 3) (x y :R) :ev (block a k) x y=form a k x y := by
  simp only [ev,py,block,form,zWe,map_monomial,eval_finsetSum,
    coe_evalRingHom,eval_monomial]
variable {E :Type} [zrb E] {A:Equation E}
private theorem dx_block (a :Index A→Closure E) (k :Fin 3) (x y :Closure E) :
    (px (block a k) y).derivative.eval x=D6 a k x y := by
  simp only [px,block,eval_finsetSum,eval_monomial,derivative_sum,← C_pow,
    derivative_mul,derivative_C,mul_zero,add_zero,derivative_monomial,eval_mul,eval_C,
    D6]
private theorem dy_block (a :Index A→Closure E) (k :Fin 3) (x y :Closure E) :
    (py (block a k) x).derivative.eval y=partialY a k x y := by
  simp only [py,block,zWe,map_monomial,coe_evalRingHom,eval_monomial,
    derivative_sum,derivative_monomial,eval_finsetSum,partialY]
  exact zUo rfl fun u _=> by ring
theorem proof :qFQL0Vc.c2 := by
  intro E _ _ A C B z
  have hblock (k :Fin 3) :
      map₂ zbO (block (ic C z) k)=block (alpha C) k := by
    rw [map_block]
    congr 1
    funext r
    simp [ic]
  have Ua (i:Fin B.size) : ∃ x y :Series E,
      zbO x=B.x i∧zbO y=B.y i ∧
      form (ic C z) 0 x y=0∧form (ic C z) 1 x y=0:= by
    obtain ⟨x,y,hx,hy,hf,hg⟩:=lift (block (ic C z) 0) (block (ic C z) 1)
      (B.x i) (B.y i) (by simpa only [hblock,eval_block] using B.f_zero i)
      (by simpa only [hblock,eval_block] using B.g_zero i)
      (by simpa only [hblock,dx_block,dy_block,jacobian] using B.simple i)
    exact ⟨x,y,hx,hy,by simpa only [eval_block] using hf,
      by simpa only [eval_block] using hg⟩
  choose x y hx hy hf hg using Ua
  exact ⟨⟨x,y,hx,hy,hf,hg⟩⟩
end
end P5_7_1_7_4_3_4_2_2_2
end
section
namespace qFQL0Vc
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil)
open qfbIfsd (Slot baseCap ordCap const₂ actual)
variable {E :Type} [Field E]
variable [Algebra L E] {A:Equation E}
theorem alpha_pencil (C : Pencil A) (u : Slot A.s (baseCap A 1) (ordCap A 1)) :
    alpha C ⟨1,u⟩ = parameter (Polynomial.C ((C.num.coeff u.1).coeff u.2)) -
      parameter (Polynomial.C ((C.den.coeff u.1).coeff u.2)) * parameter Polynomial.X := by
  simp [alpha, actual, const₂]
end
end qFQL0Vc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_1_7_4_3_4_2_2_1
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation EC seed amm jU KM polar)
open P5_7_1_7_4_3_4 (Pencil PencilBound gauge)
open qfbIfsd (Slot form actual const₂ gaugeForm)
open qFQL0Vc (Closure parameter constants alpha beta D6 partialY jacobian)
open qZu9hjc (physicalDeriv)
open qApzjua (pairEval pencilJac pairEval_comp root_coordinates root_zero map_pencilJac)
open private coeff_physical from ProximityPrize.SubmissionLower.ZpQKUZd
variable {E :Type} [zrb E]
private def dM (p:E[X][X]) (s b d:ℕ) :Prop :=
  p.natDegree≤d ∧ ∀ i≤d,(p.coeff i).natDegree≤b+(d-i)*s
private theorem fits_of_weight {p:E[X][X]} {s b d:ℕ} (hd:p.natDegree≤d)
    (h : ∀ i,(p.coeff i).natDegree+i*s≤b+d*s∨p.coeff i=0) :
    dM p s b d:= by
  refine ⟨hd,fun i hi => ?_⟩
  rcases h i with hw | hz
  · rw [← Nat.sub_add_cancel hi,Nat.add_mul] at hw
    omega
  · simp [hz]
private theorem eval_deriv_sum {R F:Type} [za6 R] [zrb F]
    (j:R →+* F) (x :F) {q:R[X]} {n:ℕ} (h:q.natDegree<n) :
    q.derivative.eval₂ j x =
      ∑ i:Fin n,j (q.coeff i)*(i.val :F)*x^(i.val-1) := by
  conv_lhs=>rw [q.as_sum_range_C_mul_X_pow' h]
  rw [← coe_eval₂RingHom,derivative_sum,map_sum]
  simp only [derivative_C_mul_X_pow,coe_eval₂RingHom,eval₂_C,
    map_mul,map_natCast,eval₂_X_pow]
  exact (zdx (fun i:ℕ=>j (q.coeff i)*(i:F)*x^(i-1)) n).symm
private theorem slot_eval {F:Type} [zrb F] (j:E →+* F) (x y :F)
    {p:E[X][X]} {s b d:ℕ} (h:dM p s b d) :
    (∑ u:Slot s b d,j ((p.coeff u.1).coeff u.2)*x^u.2.val*y^u.1.val) =
      pairEval j x y p:= by
  unfold pairEval
  rw [zla,coe_eval₂RingHom,eval₂_eq_sum_range' _ (zB1 h.1),
    ← zdx]
  apply zUo rfl
  intro i _
  change (∑ k :Fin (b+(d-i.val)*s+1),j ((p.coeff i).coeff k)*x^k.val*y^i.val)= _
  rw [← zkq,coe_eval₂RingHom,
    eval₂_eq_sum_range' _ (zB1 (h.2 i (zeh i.isLt))),
    ← zdx]
private theorem slot_dx {F:Type} [zrb F] (j:E →+* F) (x y :F)
    {p:E[X][X]} {s b d:ℕ} (h:dM p s b d) :
    (∑ u:Slot s b d,j ((p.coeff u.1).coeff u.2)*(u.2.val :F) *
      x^(u.2.val-1)*y^u.1.val)=pairEval j x y (physicalDeriv p) := by
  have hd: (physicalDeriv p).natDegree≤d:=natDegree_le_iff_coeff_eq_zero.mpr fun i hi=> by
    rw [coeff_physical,coeff_eq_zero_of_natDegree_lt (h.1.trans_lt hi),derivative_zero]
  unfold pairEval
  rw [zla,coe_eval₂RingHom,eval₂_eq_sum_range' _ (zB1 hd),
    ← zdx]
  apply zUo rfl
  intro i _
  change (∑ k :Fin (b+(d-i.val)*s+1),
    j ((p.coeff i).coeff k)*(k.val :F)*x^(k.val-1)*y^i.val)= _
  rw [← zkq,coeff_physical,coe_eval₂RingHom,
    eval_deriv_sum _ _ (zB1 (h.2 i (zeh i.isLt)))]
private theorem slot_dy {F:Type} [zrb F] (j:E →+* F) (x y :F)
    {p:E[X][X]} {s b d:ℕ} (h:dM p s b d) :
    (∑ u:Slot s b d,j ((p.coeff u.1).coeff u.2)*(u.1.val :F) *
      x^u.2.val*y^(u.1.val-1))=pairEval j x y p.derivative := by
  unfold pairEval
  rw [zla,coe_eval₂RingHom,eval_deriv_sum _ _ (zB1 h.1)]
  apply zUo rfl
  intro i _
  rw [coe_eval₂RingHom,
    eval₂_eq_sum_range' _ (zB1 (h.2 i (zeh i.isLt))),
    ← zdx,zkq,zkq]
  apply zUo rfl
  intro k _
  ring
variable {A:Equation E}
private theorem fits_f (A:Equation E) :dM A.f A.s A.b A.d :=
  fits_of_weight le_rfl A.weight
private theorem fits_pencil {p:E[X][X]} (h:PencilBound A p) :
    dM p A.s (A.b+A.s+1) A.d :=
  fits_of_weight h.1 (fun i=> by simpa only [Nat.add_right_comm] using h.2 i)
private theorem fits_polar (A:Equation E) (hd:2≤A.d) :
    dM A.f.derivative A.s A.b (A.d-1) := by
  refine ⟨natDegree_derivative_le _,fun i hi => ?_⟩
  have h:=(fits_f A).2 (i+1) (by omega)
  rw [coeff_derivative]
  have hb:=natDegree_mul_le (p:=A.f.coeff (i+1)) (q:=((i+1 :ℕ) :E[X]))
  rw [natDegree_natCast,add_zero] at hb
  rw [show A.d - 1 - i=A.d-(i+1) by omega]
  simpa only [Nat.cast_add,Nat.cast_one] using hb.trans h
variable [zZE L E]
abbrev Emb (C:Pencil A) :=
  letI:=C.base.toAlgebra
  EC A →ₐ[RatFunc E] Closure E
abbrev image (C:Pencil A) (σ:Emb C) :EC A →+* Closure E :=
  letI:=C.base.toAlgebra
  σ.toRingHom
abbrev phys (C:Pencil A) (σ:Emb C) :Closure E :=image C σ (amm A)
abbrev ord (C:Pencil A) (σ:Emb C) :Closure E :=image C σ (jU A false)
private abbrev pO (E :Type) [zrb E] :E →+* Closure E :=
  (parameter (E :=E)).comp Polynomial.C
theorem seed_image (C:Pencil A) (σ:Emb C) :
    (image C σ).comp (seed A)=pO E := by
  let _:=C.base.toAlgebra
  apply RingHom.ext
  intro c
  change σ (seed A c)=parameter (Polynomial.C c)
  rw [← C.base_seed c]
  exact (σ.commutes (RatFunc.C c)).trans (by simp [parameter,RatFunc.algebraMap_C])
private theorem parameter_image (C:Pencil A) (σ:Emb C) :
    image C σ (C.base RatFunc.X)=parameter (z7y:E[X]) := by
  let _:=C.base.toAlgebra
  exact (σ.commutes RatFunc.X).trans (by simp [parameter,RatFunc.algebraMap_X])
private theorem chart_image (C:Pencil A) (σ:Emb C) :
    pairEval (pO E) (phys C σ) (ord C σ)=(image C σ).comp (KM A false) := by
  rw [← root_coordinates,pairEval_comp,seed_image]
private theorem alpha_f (C:Pencil A) (u:Slot A.s A.b A.d) :
    alpha C ⟨0,u⟩=pO E ((A.f.coeff u.1).coeff u.2) := by
  simp [alpha,actual,const₂,pO]
private theorem alpha_p (C:Pencil A) (u:Slot A.s A.b (A.d-1)) :
    alpha C ⟨2,u⟩=pO E ((A.f.derivative.coeff u.1).coeff u.2) := by
  simp [alpha,actual,const₂,pO]
private theorem sum_pencil (C:Pencil A) (M:Slot A.s (A.b+A.s+1) A.d→Closure E) :
    (∑ u,alpha C ⟨1,u⟩*M u) =
      (∑ u,pO E ((C.num.coeff u.1).coeff u.2)*M u) -
      parameter z7y*(∑ u,pO E ((C.den.coeff u.1).coeff u.2)*M u) := by
  rw [Finset.mul_sum,← zQq]
  apply zUo rfl
  intro u _
  rw [qFQL0Vc.alpha_pencil]
  simp only [pO,zQb]
  ring
theorem first_zero (C:Pencil A) (σ:Emb C) :
    form (alpha C) 0 (phys C σ) (ord C σ)=0:= by
  unfold form
  simp_rw [alpha_f]
  have h:=slot_eval (pO E) (phys C σ) (ord C σ) (fits_f A)
  rw [chart_image,zQb,root_zero,map_zero] at h
  exact h
theorem second_zero (C:Pencil A) (σ:Emb C) :
    form (alpha C) 1 (phys C σ) (ord C σ)=0:= by
  unfold form
  simp only [mul_assoc,sum_pencil C]
  simp only [← mul_assoc,slot_eval _ _ _ (fits_pencil C.num_weight),
    slot_eval _ _ _ (fits_pencil C.den_weight),chart_image,← parameter_image C σ]
  simp only [zQb,← map_mul,← map_sub]
  rw [(eq_div_iff C.den_ne).mp C.base_X,sub_self,map_zero]
theorem spectral_num (C:Pencil A) (σ:Emb C) (hd:2≤A.d) :
    form (alpha C) 2 (phys C σ) (ord C σ)=image C σ (polar A false) := by
  unfold form
  simp_rw [alpha_p]
  have h:=slot_eval (pO E) (phys C σ) (ord C σ) (fits_polar A hd)
  rw [chart_image,zQb] at h
  exact h
theorem simple (C:Pencil A) (σ:Emb C) :
    jacobian (alpha C) (phys C σ) (ord C σ)≠0:= by
  have hx0:D6 (alpha C) 0 (phys C σ) (ord C σ) =
      pairEval (pO E) (phys C σ) (ord C σ) (physicalDeriv A.f) := by
    unfold D6
    simp_rw [alpha_f]
    exact slot_dx _ _ _ (fits_f A)
  have hy0:partialY (alpha C) 0 (phys C σ) (ord C σ) =
      pairEval (pO E) (phys C σ) (ord C σ) A.f.derivative := by
    unfold partialY
    simp_rw [alpha_f]
    exact slot_dy _ _ _ (fits_f A)
  have hx1 :D6 (alpha C) 1 (phys C σ) (ord C σ) =
      pairEval (pO E) (phys C σ) (ord C σ) (physicalDeriv C.num) -
      parameter z7y*pairEval (pO E) (phys C σ) (ord C σ) (physicalDeriv C.den) := by
    unfold D6
    simp only [mul_assoc,sum_pencil C]
    simp only [← mul_assoc,slot_dx _ _ _ (fits_pencil C.num_weight),
      slot_dx _ _ _ (fits_pencil C.den_weight)]
  have hy1 :partialY (alpha C) 1 (phys C σ) (ord C σ) =
      pairEval (pO E) (phys C σ) (ord C σ) C.num.derivative -
      parameter z7y*pairEval (pO E) (phys C σ) (ord C σ) C.den.derivative := by
    unfold partialY
    simp only [mul_assoc,sum_pencil C]
    simp only [← mul_assoc,slot_dy _ _ _ (fits_pencil C.num_weight),
      slot_dy _ _ _ (fits_pencil C.den_weight)]
  rw [jacobian,hx0,hy0,hx1,hy1,chart_image,← parameter_image C σ]
  change pencilJac ((image C σ).comp (KM A false)) A.f C.num C.den
    (image C σ (C.base RatFunc.X))≠0
  rw [← map_pencilJac]
  exact (map_ne_zero (image C σ)).mpr (q4izpTc.proof A C)
theorem spectral_den (C:Pencil A) (σ:Emb C) :
    form (beta C) 2 (phys C σ) (ord C σ) = -image C σ (gauge A C.tilt^(A.d-2)) := by
  let q:=gaugeForm C.tilt A.d
  have hq:q.natDegree<(A.d-1)+1 := by
    have hlin: (1+Polynomial.C C.tilt*z7y).natDegree≤1 :=
      natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    exact (natDegree_pow_le_of_le _ hlin).trans_lt (by simpa using (show A.d-2<A.d-1+1 by omega))
  have hconst:constants (E :=E) C.tilt=image C σ (seed A (algebraMap L E C.tilt)) :=
    (zLs (seed_image C σ) _).symm
  have hev :q.eval₂ (constants (E :=E)) (ord C σ) =
      image C σ (gauge A C.tilt^(A.d-2)) := by
    unfold q gaugeForm
    rw [← coe_eval₂RingHom,map_pow,map_add,map_one,map_mul,coe_eval₂RingHom,
      eval₂_C,eval₂_X,hconst]
    change (1+image C σ (seed A (algebraMap L E C.tilt)) *
      image C σ (jU A false))^(A.d-2)=image C σ (P5_7_1_7_4_3_4.gauge A C.tilt^(A.d-2))
    rw [P5_7_1_7_4_3_4.gauge,map_pow,map_add,map_one,map_mul]
    rfl
  unfold form
  rw [← hev,eval₂_eq_sum_range' _ hq,← zdx,zla,← Finset.sum_neg_distrib]
  apply zUo rfl
  intro i _
  change (∑ j:Fin (A.b+(A.d-1-i.val)*A.s+1),
    beta C ⟨2,⟨i,j⟩⟩*phys C σ^j.val*ord C σ^i.val)= _
  rw [Finset.sum_eq_single (0:Fin (A.b+(A.d-1-i.val)*A.s+1))]
  · simp [qFQL0Vc.beta_polar,q]
  · intro j _ hj
    have hj' : j.val≠0:= fun h=>hj (Fin.ext h)
    simp [qFQL0Vc.beta_polar,hj']
  · simp
end
end P5_7_1_7_4_3_4_2_2_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_1_7_4_3_4_2_2_1
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation EC)
open P5_7_1_7_4_3_4 (Pencil relativePolar)
open qfbIfsd (Slot baseCap ordCap form)
open qFQL0Vc (Closure alpha beta D6 jacobian)
open qApzjua (root_hom_ext)
private theorem charpoly_split {K F Ω:Type} [zrb K] [zrb F] [zrb Ω]
    [zZE K F] [zZE K Ω] [Module.Finite K F] [Algebra.IsSeparable K F]
    [IsAlgClosed Ω] [Infinite K] (q:F) :
    (zXA K F q).charpoly.map (algebraMap K Ω) =
      ∏ σ:F →ₐ[K] Ω,(z7y - C (σ q)) := by
  classical
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective (algebraMap K Ω).injective).mono ?_
  rintro _ ⟨t,rfl⟩
  change Polynomial.eval (algebraMap K Ω t) _ = _
  rw [Polynomial.eval_map_algebraMap,Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    LinearMap.eval_charpoly]
  have hs :zXA K F (algebraMap K F t) =
      algebraMap K (Module.End K F) t:=(zXA K F).commutes t
  rw [← hs,← map_sub,← Algebra.norm_apply,Algebra.norm_eq_prod_embeddings K Ω]
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    map_sub,AlgHom.commutes]
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
private theorem zero_weight_x (C:Pencil A) (hb:A.b=0) (hs :A.s=0)
    {x x' y :Closure E}
    (hf :form (alpha C) 1 x y=0) (hg:form (alpha C) 1 x' y=0)
    (hj:jacobian (alpha C) x y≠0) :x=x' := by
  have h0:D6 (alpha C) 0 x y=0:= by
    unfold D6
    apply Finset.sum_eq_zero
    intro u _
    have hu:=u.2.isLt
    change u.2.val<A.b+(A.d-u.1.val)*A.s+1 at hu
    have h:u.2.val=0:= by simpa [hb,hs] using hu
    simp [h]
  have h1 :D6 (alpha C) 1 x y≠0:= by
    intro h
    exact hj (by simp [jacobian,h0,h])
  have hdiff :form (alpha C) 1 x y - form (alpha C) 1 x' y =
      (x-x')*D6 (alpha C) 1 x y := by
    unfold form D6
    rw [← zQq,Finset.mul_sum]
    apply zUo rfl
    intro u _
    have hu:=u.2.isLt
    change u.2.val<(A.b+A.s+1)+(A.d-u.1.val)*A.s+1 at hu
    have h:u.2.val<2 := by simpa [hb,hs] using hu
    interval_cases u.2.val
    · simp
    · simp
      ring
  rw [hf,hg,sub_self] at hdiff
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff.symm).resolve_right h1)
private theorem scale_ne (C:Pencil A) (σ:Emb C) :
    form (beta C) 2 (phys C σ) (ord C σ)≠0:= by
  rw [spectral_den,neg_ne_zero,map_pow]
  exact pow_ne_zero _ ((map_ne_zero (image C σ)).mpr C.gauge_ne)
private theorem separates (C:Pencil A) (hd:2≤A.d) (σ τ:Emb C) (hne :σ≠τ) :
    ∃ u:Slot A.s (baseCap A 2) (ordCap A 2),
      phys C σ^u.2.val*ord C σ^u.1.val/form (beta C) 2 (phys C σ) (ord C σ) ≠
      phys C τ^u.2.val*ord C τ^u.1.val/form (beta C) 2 (phys C τ) (ord C τ) := by
  classical
  by_contra! hall
  let c:Slot A.s A.b (A.d-1) :=⟨0,0⟩
  let y :Slot A.s A.b (A.d-1) :=⟨⟨1,by omega⟩,0⟩
  let S:=form (beta C) 2 (phys C σ) (ord C σ)
  let T:=form (beta C) 2 (phys C τ) (ord C τ)
  have hS:S≠0:=scale_ne C σ
  have h0:S=T:= by
    have h: (1 :Closure E)/S=1/T:= by simpa [c,S,T] using hall c
    simpa only [one_div,inv_inj] using h
  have hy :ord C σ=ord C τ:= by
    have h:ord C σ/S=ord C τ/T:= by simpa [y,S,T] using hall y
    rw [← h0] at h
    exact (div_left_inj' hS).mp h
  have hx :phys C σ=phys C τ:= by
    by_cases h:A.b+A.s=0
    · have hb:A.b=0:= by omega
      have hs :A.s=0:= by omega
      exact zero_weight_x C hb hs (second_zero C σ) (hy.symm ▸ second_zero C τ) (simple C σ)
    · let x :Slot A.s A.b (A.d-1) :=
        ⟨0,⟨1,by
          change 1<A.b+(A.d-1)*A.s+1
          have hm:=Nat.mul_le_mul_right A.s (show 1≤A.d-1 by omega)
          simp only [one_mul] at hm
          omega⟩⟩
      have he :phys C σ/S=phys C τ/T:= by simpa [x,S,T] using hall x
      rw [← h0] at he
      exact (div_left_inj' hS).mp he
  apply hne
  let _:=C.base.toAlgebra
  apply AlgHom.ext
  intro a
  exact zLs (root_hom_ext
    ((seed_image C σ).trans (seed_image C τ).symm) hx hy) a
theorem proof :qFQL0Vc.c1 := by
  intro E _ _ A hd C
  classical
  let _:=C.base.toAlgebra
  let _:=C.finite
  let _:=C.separable
  let _:Infinite (RatFunc E) :=
    Infinite.of_injective (algebraMap E[X] (RatFunc E)) (IsFractionRing.injective _ _)
  let I:=Emb C
  let e :=(Fintype.equivFin I).symm
  refine ⟨⟨Fintype.card I,phys C ∘ e,ord C ∘ e,fun i=>first_zero C (e i),
    fun i=>second_zero C (e i),fun i=>simple C (e i),fun i=>scale_ne C (e i),
    fun i j h=>separates C hd (e i) (e j) (e.injective.ne h),?_⟩⟩
  change ((zXA (RatFunc E) (EC A) (relativePolar C)).charpoly.map
    (algebraMap (RatFunc E) (Closure E)))= _
  rw [charpoly_split]
  refine Fintype.prod_equiv e.symm _ _ (fun σ => ?_)
  have hval : -(form (alpha C) 2 (phys C σ) (ord C σ)) /
      form (beta C) 2 (phys C σ) (ord C σ)=image C σ (relativePolar C) := by
    rw [spectral_num C σ hd,spectral_den,neg_div_neg_eq,relativePolar,map_div₀]
  simp only [z3s,Equiv.apply_symm_apply,hval]
  rfl
end
end P5_7_1_7_4_3_4_2_2_1
end
section
set_option autoImplicit true
namespace qBl3Pad
noncomputable section
open scoped Classical
open cu (L)
open P5_7_1_7_4_3_4 (pairDegree)
open qfbIfsd (Slot Vars form)
end
end qBl3Pad
end
section
set_option autoImplicit true
namespace qBl3Pad
noncomputable section
open scoped Classical

open qfbIfsd (Vars kK Detects)
private theorem detects {s :ℕ} {b e :Fin 3→ℕ} {R:jo s b e}
    (hR:incidence s b e R=0) :Detects R:= by
  intro M _ m a x y hz
  let g:Fin 2 ⊕ Vars s b e→M:=Sum.elim ![x,y] a
  let f :=zOD m g
  have hcoeff (v :Vars s b e) :f (bcm v)=a v := by simp [f,g,bcm]
  have harg (v :Vars s b e) :f (incidenceArg v)=a v := by
    by_cases hv :v.2=zeroSlot s (b v.1) (e v.1)
    · have hv' : v=⟨v.1,zeroSlot s (b v.1) (e v.1)⟩:=Sigma.ext rfl (heq_of_eq hv)
      rw [incidenceArg,ite_eq_left hv,map_neg,map_rest]
      have hx :f (z9v (.inl 0))=x := by simp [f,g]
      have hy :f (z9v (.inl 1))=y := by simp [f,g]
      rw [hx,hy,show f ∘ bcm=a from funext hcoeff]
      have h:=(form_eq a v.1 x y).symm.trans (hz v.1)
      exact (neg_eq_of_add_eq_zero_left h).trans (congrArg a hv').symm
    · rw [incidenceArg,ite_eq_right hv,hcoeff]
  have hf :f.comp znf=m:= by ext l; simp [f]
  have h:=congrArg f hR
  change f (zOD znf incidenceArg R)=f 0 at h
  rw [MvPolynomial.map_eval₂Hom,hf,map_zero] at h
  simpa only [harg,MvPolynomial.coe_eval₂Hom] using h
private theorem ags {s :ℕ} {b e :Fin 3→ℕ} (R:jo s b e)
    (h : ∀ k,R.weightedTotalDegree (blockWeight k)≤ng s b e k) :
    R.totalDegree≤kK s b e := by
  rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
  intro m hm
  have hs : (∑ k :Fin 3,Finsupp.weight (blockWeight k) m)=m.sum (fun _ n=>n) := by
    simp only [Finsupp.weight_apply,Finsupp.sum]
    rw [Finset.sum_comm]
    simp [blockWeight]
  have ha : (∑ k :Fin 3,ng s b e k)=kK s b e := by
    simp only [Fin.sum_univ_three,ng,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,kK]
    ac_rfl
  rw [← hs,← ha]
  exact Finset.sum_le_sum fun k _=>(MvPolynomial.le_weightedTotalDegree _ hm).trans (h k)
theorem of_children (pairs :c1) (principal:c2) (norm:c3) :qfbIfsd.c1 := by
  intro s b e he hb
  obtain ⟨Q,hQ,hQ0,_⟩:=norm s b e he hb 0 (pairs s b e he hb 0).1
  obtain ⟨R,hR,hR0,hdiv⟩:=principal s b e he hb ⟨Q,hQ,hQ0⟩
  refine ⟨R,hR,ags R (fun k => ?_),detects hR0⟩
  obtain ⟨Qk,hQk,hk0,hdeg⟩:=norm s b e he hb k (pairs s b e he hb k).1
  exact (MvPolynomial.weightedTotalDegree_le_of_dvd _ (hdiv _ hk0) hQk).trans
    (hdeg.trans (pairs s b e he hb k).2)
end
end qBl3Pad
end
section
set_option autoImplicit true
namespace q55F46a
noncomputable section
open Polynomial Finset qNu3xvc

open qFD8jve (aFA sheetPole)
open P5_7_1_7_4_3_4 (Pencil relativePolar adG)
open cu (L)
open E7 (CurveField CurvePlace poleOrder KB)
open agN (b27 a6F)
open scoped Classical WithZero
open private rate same_center sum_le_all from ProximityPrize.SubmissionLower.P5_7_1_7_4_3_4Split
open private cfl b4u from ProximityPrize.SubmissionLower.A3
private theorem gauss_of_pencil {E :Type} [zrb E] [zZE L E] {A:Equation E}
    {r :Bool} {v :GraphVal A r} {w:CurvePlace L E} {x :L}
    (hc:CurveField L E) (C:Pencil A) (hv :Over v w x)
    (hfresh : ∀ g:L[X],g≠0 →
      v.val (g.eval₂ ((seed A).comp (algebraMap L E)) (C.base RatFunc.X))=1) :
    ∃ n:ℕ,0<n ∧ ∀ g:E[X],
      v.val (C.base (algebraMap E[X] (RatFunc E) g))=adG w.value g^n:= by
  obtain ⟨n,hn,hrest⟩:=hv.1
  refine ⟨n,hn,fun g => ?_⟩
  have hnt : ∃ t:E,t≠0∧w.value t≠1 := by
    obtain ⟨t,ht⟩:=w.normalized (WithZero.exp (-1 :ℤ))
    refine ⟨t,w.value.ne_zero_iff.mp (ht ▸ ?_),?_⟩
    · exact WithZero.exp_ne_zero
    · simp [ht]
  have hres (a :E) (ha :v.val (seed A a)≤1) :
      ∃ c:L,v.val (seed A (a-algebraMap L E c))<1 := by
    have hw:w.value a≤1 :=
      le_of_not_gt fun h=>(not_lt_of_ge ha) (hrest a ▸ one_lt_pow₀ h hn.ne')
    obtain ⟨c,h⟩:=cfl hc w.value ⟨w.on_constants⟩ hnt a hw
    refine ⟨c,?_⟩
    rw [hrest]
    simpa only [one_pow] using pow_lt_pow_left₀ h zero_le hn.ne'
  have ha :v.val (C.base RatFunc.X)=1 := by
    simpa only [eval₂_X] using hfresh z7y Polynomial.X_ne_zero
  have hs :C.base.comp RatFunc.C=seed A:=RingHom.ext C.base_seed
  have heval :C.base (algebraMap E[X] (RatFunc E) g) =
      g.eval₂ (seed A) (C.base RatFunc.X) := by
    rw [← hs,← RatFunc.algebraMap_comp_C,← RatFunc.algebraMap_X,
      ← zly,← zly,eval₂_C_X]
  rw [heval,b4u (seed A) _ v.val ha hres hfresh,adG]
  simp only [hrest]
  exact (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun a :ℤᵐ⁰=>a^n)
    (fun _ _ hab=>pow_le_pow_left₀ zero_le hab n) (zero_pow hn.ne')).symm
theorem of_children (qW:c1) (FT:P5_7_1_7_4_3_4.c2)
    (localNorm:P5_7_1_7_4_3_4.c3) :qNu3xvc.c4 := by
  intro E _ _ A hc hd hp ι _ w x r v hinj hreg hover
  obtain ⟨C,hpolar,hfresh⟩:=qW A hd hp ι w x r v hover
  have hgauss (i:ι) :=gauss_of_pencil hc C (hover i) (hfresh i)
  have hq:relativePolar C≠0:=div_ne_zero C.polar_ne (pow_ne_zero _ C.gauge_ne)
  obtain ⟨P,hP,hdvd,hbound⟩:=FT A hd C
  obtain ⟨j,hj⟩ : ∃ j,(P.coeff 0).coeff j≠0:= by
    by_contra! h
    exact hP (Polynomial.ext fun j=> by simp [h j])
  let a :=(P.coeff 0).coeff j
  let V:=univ.image w
  have hlocal (z :CurvePlace L E) (hz :z∈V) :
      (∑ i∈univ.filter (fun i=>w i=z),poleCharge (v i))≤KB z.value a := by
    obtain ⟨i,-,hi⟩:=mem_image.mp hz
    have h0:sheetPole z.value A.f=0:= by
      rw [← hi]
      exact (Finset.sup_eq_bot_iff _ _).mpr fun ij _ =>
        (a6F _ _).mpr ((hreg i).1 ij.1 ij.2)
    have hB:aFA z.value P 0:= by simpa only [h0,Nat.mul_zero] using hbound z
    have hh:=localNorm z C.base _ C.finite C.separable hq P hP hB hdvd
      (univ.filter (fun i=>w i=z)) (fun i=>(v i).val)
      (by
        intro i hi j hj h
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        have hw:=hi'.trans hj'.symm
        exact hinj (Prod.ext hw (same_center (hover i) (hw.symm ▸ hover j) h)))
      (fun i _=>(v i).normalized) (fun i hi=>(mem_filter.mp hi).2 ▸ hgauss i)
    simp only [KB,hpolar] at hh
    refine hh.trans (z0Z (neg_le_neg ?_))
    have hs :z.value a≤adG z.value (P.coeff 0) :=
      Finset.le_sup (f := fun k=>z.value ((P.coeff 0).coeff k))
        (Polynomial.mem_support_iff.mpr hj)
    exact (WithZero.log_le_log (z.value.ne_zero_iff.mpr hj)
      (ne_of_gt ((zero_lt_iff.mpr (z.value.ne_zero_iff.mpr hj)).trans_le hs))).mpr hs
  have hdiv :=aFU.of_children
    bRt.proof bRu.proof L E hc
  obtain ⟨hpf,hzf,hsum,_⟩:=hdiv a
  let M (z :CurvePlace L E) :=sheetPole z.value A.f
  have hM:M.HasFiniteSupport:=b27 hdiv _
  have hpoles : (∑ᶠ z :CurvePlace L E,poleOrder z.value a)≤polarRate A*A.h:= by
    change _≤polarRate A * ∑ᶠ z,M z
    rw [mul_finsum]
    apply finsum_le_finsum hpf
      (hM.subset fun z hz hzero=>hz (by change polarRate A*M z=0; rw [hzero,mul_zero]))
    intro z
    have hb:=hbound z 0 j
    rw [rate A hd] at hb
    exact z0Z ((WithZero.log_le_iff_le_exp (z.value.ne_zero_iff.mpr hj)).mpr hb)
  calc
    (∑ i,poleCharge (v i)) =
        ∑ z∈V,∑ i∈univ.filter (fun i=>w i=z),poleCharge (v i) :=
      (sum_fiberwise_of_maps_to (fun _ hi=>mem_image_of_mem _ hi) _).symm
    _ ≤ ∑ z∈V,KB z.value a :=sum_le_sum hlocal
    _ ≤ ∑ᶠ z :CurvePlace L E,KB z.value a :=sum_le_all _ hzf _
    _ = ∑ᶠ z :CurvePlace L E,poleOrder z.value a :=hsum.symm
    _≤_:=hpoles
end
end q55F46a
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qav6Dra
theorem proof :qO4n7sd.c3 :=
  q55F46a.of_children
    (qTFhFCb.of_children P5_7_1_7Q434R12.proof1 P5_7_1_7Q434R12.proof)
    (qfbIfsd.of_children
      (qBl3Pad.of_children qVEB2pd.proof qOuTtVa.proof
        qDttdYd.proof)
      (qFQL0Vc.of_children P5_7_1_7_4_3_4_2_2_1.proof P5_7_1_7_4_3_4_2_2_2.proof))
    P5_7_1_7Q434.proof
end qav6Dra
end
