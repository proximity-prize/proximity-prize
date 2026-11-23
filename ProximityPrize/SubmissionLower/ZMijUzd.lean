import ProximityPrize.SubmissionLower.ZitKCce
set_option Elab.async false
open _root_ renaming Algebra.adjoin → zum, Algebra.subset_adjoin → zkk, Field → zrb, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Fintype → z85, Function.Injective → zq4, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_eq → zYY, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aeval_X → zTw, MvPolynomial.eval → zY9, MvPolynomial.eval_X → zV6, Nat.le_of_lt_succ → zeh, RingHom.id → zz4, RingHom.id_apply → z6n, Set.range → zxp
section
set_option backward.isDefEq.respectTransparency false
namespace qaTRbFe
noncomputable section
open Polynomial
open q8Z6NHc (Slot jo Generic)
open qG7TGJa (aFB Zk)
private def nested {R σ:Type} [CommSemiring R] [z85 σ]
   (i j:σ→ℕ) (c:σ→R) :R[X][X] :=
 ∑ t,monomial (i t) (monomial (j t) (c t))
private theorem nested_map {R S σ:Type} [CommSemiring R] [CommSemiring S] [z85 σ]
  (φ:R →+* S) (i j:σ→ℕ) (c:σ→R) :
  (nested i j c).map (mapRingHom φ)=nested i j (fun t=>φ (c t)) := by
 simp only [nested,Polynomial.map_sum,map_monomial,coe_mapRingHom]
private theorem nested_degree {R σ:Type} [CommSemiring R] [z85 σ]
  (i j:σ→ℕ) (c:σ→R) {m:ℕ} (h : ∀ t,i t≤ m) :
  (nested i j c).natDegree≤ m :=
 natDegree_sum_le_of_forall_le _ _ fun t _=>(natDegree_monomial_le _).trans (h t)
private theorem nested_single {R σ:Type} [CommSemiring R] [z85 σ] [DecidableEq σ]
   (i j:σ→ℕ) (u:σ) (hu:j u=0) :
   nested i j (fun t=>if t=u then (1 :R) else 0) =
     (Polynomial.X:R[X][X])^i u:= by
 unfold nested
 rw [zi6 u]
 · simp [hu,monomial_one_right_eq_X_pow]
 · intro t _ ht
   simp [ht]
 · simp
private theorem nested_flip {E σ:Type} [zrb E] [z85 σ]
   (i j:σ→ℕ) (c:σ→E) (x y :E) :
   (nested i j c).eval₂ (evalRingHom x) y =
     (nested j i c).eval₂ (evalRingHom y) x := by
 simp only [nested,eval₂_finsetSum,eval₂_monomial,coe_evalRingHom,← eval₂_id]
 apply zUo rfl
 intro t _
 simp only [z6n]
 rw [mul_right_comm]
private theorem projection {R E σ τ:Type} [zrb R] [zrb E] [z85 σ] [z85 τ]
    (φ:MvPolynomial (σ ⊕ τ) R →+* E) (hφ:zq4 φ)
    (i j:σ→ℕ) (k l:τ→ℕ) (u:σ) (v :τ) {n:ℕ}
    (hu:j u=0) (hv :k v=0) (hv' : l v=0)
    (hi : ∀ t,i t≤ i u) (hk : ∀ t,k t≤n) (hn:n≠0) :
    ∃ P:E[X],P≠0 ∧ ∀ x y :E,
      (nested i j (fun t=>φ (z9v (Sum.inl t)))).eval₂ (evalRingHom x) y=0 →
      (nested k l (fun t=>φ (z9v (Sum.inr t)))).eval₂ (evalRingHom x) y=0 →
      IsRoot P x := by
  classical
  let A:=MvPolynomial (σ ⊕ τ) R
  let f :A[X][X] :=nested i j fun t=>z9v (Sum.inl t)
  let g:A[X][X] :=nested k l fun t=>z9v (Sum.inr t)
  let ψ:A →+* R:=zY9
    (Sum.elim (fun t=>if t=u then 1 else 0) (fun t=>if t=v then 1 else 0))
  have hf :f.map (mapRingHom ψ)=(Polynomial.X:R[X][X])^i u:= by
    change (nested i j _).map (mapRingHom ψ)= _
    rw [nested_map]
    have h: (fun t:σ=>ψ (z9v (Sum.inl t))) =
        (fun t=>if t=u then 1 else 0) :=funext fun t=>zV6 (Sum.inl t)
    rw [h,nested_single i j u hu]
  have hg:g.map (mapRingHom ψ)=1 := by
    change (nested k l _).map (mapRingHom ψ)= _
    rw [nested_map]
    have h: (fun t:τ=>ψ (z9v (Sum.inr t))) =
        (fun t=>if t=v then 1 else 0) :=funext fun t=>zV6 (Sum.inr t)
    rw [h,nested_single k l v hv',hv,pow_zero]
  let P:=f.resultant g (i u) n
  have hP:P≠0:= by
    intro h
    have hs :P.map ψ=0:= by rw [h,Polynomial.map_zero]
    change mapRingHom ψ (f.resultant g (i u) n)=0 at hs
    rw [← resultant_map_map,hf,hg,resultant_one_right,coeff_X_pow_self,one_pow] at hs
    exact one_ne_zero hs
  refine ⟨P.map φ,(Polynomial.map_ne_zero_iff hφ).mpr hP,?_⟩
  intro x y hx hy
  let F:=nested i j fun t=>φ (z9v (Sum.inl t))
  let G:=nested k l fun t=>φ (z9v (Sum.inr t))
  have hF:f.map (mapRingHom φ)=F:=nested_map φ i j _
  have hG:g.map (mapRingHom φ)=G:=nested_map φ k l _
  obtain ⟨U,V,_,_,h⟩:=exists_mul_add_mul_eq_C_resultant F G
    (nested_degree i j _ hi) (nested_degree k l _ hk) (Or.inr hn)
  have he :=congrArg (eval₂RingHom (evalRingHom x) y) h
  change IsRoot (mapRingHom φ (f.resultant g (i u) n)) x
  rw [← resultant_map_map,hF,hG]
  change (F.resultant G (i u) n).eval x=0
  change F.eval₂ (evalRingHom x) y=0 at hx
  change G.eval₂ (evalRingHom x) y=0 at hy
  simpa only [coe_eval₂RingHom,eval₂_add,eval₂_mul,eval₂_C,hx,hy,zero_mul,
    add_zero,coe_evalRingHom] using he.symm
private def outer {d s a :ℕ} (t:Slot d s a) :ℕ:=t.val.1.val
private def inner {d s a :ℕ} (t:Slot d s a) :ℕ:=t.val.2.val
private def slot {d s a :ℕ} (i j:ℕ) (hi:i≤d) (hj:j+i*s≤a) :Slot d s a :=
 ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hj⟩
theorem proof :qG7TGJa.c1 := by
  intro d s a hd _ hweight
  let b:=a+s+1
  let φ:=algebraMap (jo d s a) (Generic d s a)
  have hφ:zq4 φ:= by
    rw [show φ= _ from zYY
      (jo d s a) (aFB d s a) (Generic d s a)]
    exact (algebraMap (aFB d s a) (Generic d s a)).injective.comp
      (zxb (jo d s a) (aFB d s a))
  let v :Slot d s b:=slot 0 0 (Nat.zero_le _) (by simp)
  let uy :Slot d s a :=slot d 0 le_rfl (by simpa using hweight)
  let ux :Slot d s a :=slot 0 a (Nat.zero_le _) (by simp)
  obtain ⟨P,hP,hp⟩:=projection φ hφ outer inner outer inner uy v
    (n:=d) rfl rfl rfl (fun t=>zeh t.val.1.isLt)
    (fun t=>zeh t.val.1.isLt) (by omega)
  obtain ⟨Q,hQ,hq⟩:=projection φ hφ inner outer inner outer ux v
    (n:=b) rfl rfl rfl (fun t=>zeh t.val.2.isLt)
    (fun t=>zeh t.val.2.isLt) (by dsimp [b]; omega)
  have roots (q:Zk d s a) :IsRoot P q.val.1∧IsRoot Q q.val.2 := by
    have hf : (nested outer inner
        (fun t:Slot d s a=>φ (z9v (Sum.inl t)))).eval₂
          (evalRingHom q.val.1) q.val.2=0:=q.prop.1
    have hg: (nested outer inner
        (fun t:Slot d s b=>φ (z9v (Sum.inr t)))).eval₂
          (evalRingHom q.val.1) q.val.2=0:=q.prop.2
    refine ⟨hp _ _ hf hg,hq q.val.2 q.val.1 ?_ ?_⟩
    · rw [← nested_flip]
      exact hf
    · rw [← nested_flip]
      exact hg
  let _:Finite {x // IsRoot P x} := (finite_setOfPred_isRoot hP).to_subtype
  let _:Finite {y // IsRoot Q y} := (finite_setOfPred_isRoot hQ).to_subtype
  let toRoots (q:Zk d s a) : {x // IsRoot P x} × {y // IsRoot Q y} :=
    (⟨q.val.1,(roots q).1⟩,⟨q.val.2,(roots q).2⟩)
  apply Finite.of_injective toRoots
  intro q r h
  exact Subtype.ext (Prod.ext
    (congrArg (fun z=>z.1.val) h) (congrArg (fun z=>z.2.val) h))
end
end qaTRbFe
end
section
namespace qqgIGhd
noncomputable section
open Polynomial
open cu (L)
open qZu9hjc (atPair physicalDeriv jacobian gauge)
open q8Z6NHc (Slot Index jo Generic form genericF genericG)
open qG7TGJa (Zk aFB)
private theorem independent_of_span {k E I:Type} [zrb k] [zrb E]
  [Algebra k E] [Finite I] {v w:I→E} (hv :AlgebraicIndependent k v)
  (h : ∀ i,v i∈zum k (zxp w)) :
  AlgebraicIndependent k w:= by
 let S:=zum k (zxp w)
 let v' (i:I) :S:=⟨v i,h i⟩
 let w' (i:I) :S:=⟨w i,zkk ⟨i,rfl⟩⟩
 have hv' : AlgebraicIndependent k v' := AlgebraicIndependent.of_comp S.val hv
 have htop:zum k (zxp w') = ⊤ := by
  apply Subalgebra.map_injective (f :=S.val) Subtype.val_injective
  rw [Algebra.map_top,Subalgebra.range_val,← Algebra.adjoin_image,← Set.range_comp]
  rfl
 let:Algebra.IsAlgebraic (zum k (zxp w')) S:=⟨fun z=> by
  have hz :z∈zum k (zxp w') := by rw [htop]; exact Algebra.mem_top
  exact isAlgebraic_algebraMap (⟨z,hz⟩:zum k (zxp w'))⟩
 have hw' := (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k w'
  hv'.cardinalMk_le_trdeg).1
 exact hw'.map' (f :=S.val) Subtype.val_injective
private def constant (d s a :ℕ) :Slot d s a :=
 ⟨(0,0),by simp⟩
private def jU {d s a :ℕ} (hd:2≤d) (hs :d*s≤a) :Slot d s a :=
 ⟨(⟨1,by omega⟩,0),by
   have h:=Nat.mul_le_mul_right s (show 1≤d by omega)
   simpa using h.trans hs⟩
private def KK (d s a :ℕ) :Slot d s (a+s+1) :=
 ⟨(0,⟨1,by omega⟩),by simp⟩
private def ajS {R:Type} [CommSemiring R] {d s a :ℕ} (u:Slot d s a→R)
   (x y :R) (w m n:Slot d s a→ℕ) :R :=
 ∑ i,u i*(w i:R)*x^m i*y ^n i
private abbrev dx {R:Type} [CommSemiring R] {d s a :ℕ} (u:Slot d s a→R)
  (x y :R) :R :=
 ajS u x y (fun i=>i.val.2.val) (fun i=>i.val.2.val - 1) (fun i=>i.val.1.val)
private abbrev dy {R:Type} [CommSemiring R] {d s a :ℕ} (u:Slot d s a→R)
  (x y :R) :R :=
 ajS u x y (fun i=>i.val.1.val) (fun i=>i.val.2.val) (fun i=>i.val.1.val - 1)
private theorem map_moment {R S H :Type} [CommSemiring R] [CommSemiring S]
  [FunLike H R S] [RingHomClass H R S] {d s a :ℕ}
  (f :H) (u:Slot d s a→R) (x y :R) (w m n:Slot d s a→ℕ) :
  f (ajS u x y w m n)=ajS (fun i=>f (u i)) (f x) (f y) w m n:= by
 simp only [ajS,map_sum,map_mul,map_pow,map_natCast]
private theorem moment_congr {R:Type} [CommSemiring R] {d s a :ℕ} {u v :Slot d s a→R}
   (x y :R) (w m n:Slot d s a→ℕ) (i₀:Slot d s a)
   (h₀:w i₀=0) (h : ∀ i,i≠i₀→u i=v i) :
   ajS u x y w m n=ajS v x y w m n:= by
 classical
 apply zUo rfl
 intro i _
 by_cases hi:i=i₀
 · subst i
   simp [h₀]
 · rw [h i hi]
private theorem moment_single {R:Type} [CommSemiring R] {d s a :ℕ}
  (u:Slot d s a→R) (x y :R) (w m n:Slot d s a→ℕ) (i₀:Slot d s a)
  (h : ∀ i,i≠i₀→u i=0) :
  ajS u x y w m n=u i₀*(w i₀:R)*x^m i₀*y ^n i₀:= by
 classical
 unfold ajS
 exact zi6 i₀ (fun i _ hi=> by simp [h i hi]) (by simp)
private theorem at_form {E :Type} [zrb E] {d s a :ℕ} (u:Slot d s a→E) (x y :E) :
  atPair (zz4 E) x y (form u) = ∑ i,u i*x^i.val.2.val*y ^i.val.1.val := by
 change (eval₂RingHom (eval₂RingHom (zz4 E) x) y) (form u)= _
 simp only [form,map_sum,coe_eval₂RingHom,eval₂_monomial,z6n]
private theorem coeff_physical {E :Type} [zrb E] (f :E[X][X]) (i:ℕ) :
   (physicalDeriv f).coeff i=(f.coeff i).derivative := by
 classical
 by_cases h:i∈f.support
 · simp [physicalDeriv,sum_def,coeff_monomial,h]
 · simp [physicalDeriv,sum_def,coeff_monomial,h,notMem_support_iff.mp h]
private theorem at_dx {E :Type} [zrb E] {d s a :ℕ} (u:Slot d s a→E) (x y :E) :
  atPair (zz4 E) x y (physicalDeriv (form u))=dx u x y := by
 have hf :physicalDeriv (form u) =
   ∑ i,monomial i.val.1.val ((monomial i.val.2.val (u i)).derivative) := by
  apply Polynomial.ext
  intro n
  simp only [coeff_physical,form,finsetSum_coeff,derivative_sum,coeff_monomial]
  exact zUo rfl (fun i _=> by split <;> simp_all)
 change (eval₂RingHom (eval₂RingHom (zz4 E) x) y) _ = _
 simp only [hf,map_sum,coe_eval₂RingHom,eval₂_monomial,derivative_monomial,
  z6n,ajS]
private theorem at_dy {E :Type} [zrb E] {d s a :ℕ} (u:Slot d s a→E) (x y :E) :
  atPair (zz4 E) x y (form u).derivative=dy u x y := by
 change (eval₂RingHom (eval₂RingHom (zz4 E) x) y) _ = _
 simp only [form,map_sum,coe_eval₂RingHom,derivative_monomial,
  eval₂_monomial,map_mul,map_natCast,z6n,ajS]
 exact zUo rfl (fun _ _=> by ac_rfl)
variable {d s a :ℕ}
local notation "I" => Index d s a
local notation "D" => jo d s a
local notation "E" => Generic d s a
private def original (i:I) :E :=algebraMap D E (z9v i)
private def replaced (q:Zk d s a) :I→E
 | .inl i=>if i=constant d s a then q.val.1 else original (.inl i)
 | .inr i=>if i=constant d s (a+s+1) then q.val.2 else original (.inr i)
private theorem replaced_x (q:Zk d s a) :
 replaced q (.inl (constant d s a))=q.val.1 := by simp [replaced]
private theorem replaced_y (q:Zk d s a) :
 replaced q (.inr (constant d s (a+s+1)))=q.val.2 := by simp [replaced]
private theorem cHU {F:Type} [zrb F] [Algebra L F] {n:ℕ} (S:Subalgebra L F)
    (u:Slot d s n→F) (x y :F) (hx :x∈S) (hy :y∈S)
    (h : ∀ i,i≠constant d s n→u i∈S)
    (hz :atPair (zz4 F) x y (form u)=0) :
    u (constant d s n)∈S:= by
  classical
  rw [at_form,← Finset.sum_erase_add _ _ (Finset.mem_univ (constant d s n))] at hz
  have hsum :
      (∑ i∈Finset.univ.erase (constant d s n),
        u i*x^i.val.2.val*y ^i.val.1.val)∈S :=
    S.sum_mem (fun i hi=>S.mul_mem (S.mul_mem (h i (Finset.ne_of_mem_erase hi))
      (S.pow_mem hx _)) (S.pow_mem hy _))
  have h0: (constant d s n).val.1.val=0:=rfl
  have h1 : (constant d s n).val.2.val=0:=rfl
  simp only [h0,h1,pow_zero,mul_one] at hz
  rw [eq_neg_of_add_eq_zero_right hz]
  exact S.neg_mem hsum
private theorem replaced_independent (q:Zk d s a) :AlgebraicIndependent L (replaced q) := by
 have hj:zq4 (algebraMap D E) := by
   rw [zYY D (aFB d s a) E]
   exact (algebraMap (aFB d s a) E).injective.comp (zxb D (aFB d s a))
 have hv :AlgebraicIndependent L (original (d:=d) (s :=s) (a :=a)) :=
   (MvPolynomial.algebraicIndependent_X I L).map' (f :=IsScalarTower.toAlgHom L D E) hj
 apply independent_of_span hv
 let S:=zum L (zxp (replaced q))
 have hmem (i:I) :replaced q i∈S:=zkk ⟨i,rfl⟩
 have hx :q.val.1∈S:= by simpa only [replaced_x] using hmem (.inl (constant d s a))
 have hy :q.val.2∈S:= by simpa only [replaced_y] using hmem (.inr (constant d s (a+s+1)))
 have hl (i:Slot d s a) (hi:i≠constant d s a) :original (.inl i)∈S:= by
   simpa [replaced,hi] using hmem (.inl i)
 have hr (i:Slot d s (a+s+1)) (hi:i≠constant d s (a+s+1)) :original (.inr i)∈S:= by
   simpa [replaced,hi] using hmem (.inr i)
 intro i
 change original i∈S
 cases i with
 | inl i =>
   by_cases hi:i=constant d s a
   · subst i
     exact cHU S (fun i=>original (.inl i)) _ _ hx hy hl q.prop.1
   · exact hl i hi
 | inr i =>
   by_cases hi:i=constant d s (a+s+1)
   · subst i
     exact cHU S (fun i=>original (.inr i)) _ _ hx hy hr q.prop.2
   · exact hr i hi
private def jacPoly (d s a :ℕ) :jo d s a :=
 let u (i:Slot d s a) :jo d s a :=z9v (.inl i)
 let v (i:Slot d s (a+s+1)) :jo d s a :=z9v (.inr i)
 let x :jo d s a :=z9v (.inl (constant d s a))
 let y :jo d s a :=z9v (.inr (constant d s (a+s+1)))
 dx u x y*dy v x y - dy u x y*dx v x y
private theorem eval_jac (q:Zk d s a) :
   zIe (replaced q) (jacPoly d s a) =
     jacobian (zz4 _) q.val.1 q.val.2 (genericF d s a) (genericG d s a) := by
 simp only [jacPoly,map_sub,map_mul,map_moment,zTw,
   jacobian,genericF,genericG,at_dx,at_dy]
 have hl (i:Slot d s a) (hi:i≠constant d s a) :
     replaced q (.inl i)=algebraMap D E (z9v (.inl i)) := by simp [replaced,hi,original]
 have hr (i:Slot d s (a+s+1)) (hi:i≠constant d s (a+s+1)) :
     replaced q (.inr i)=algebraMap D E (z9v (.inr i)) := by simp [replaced,hi,original]
 simp only [replaced_x,replaced_y]
 rw [moment_congr _ _ _ _ _ _ rfl hl,moment_congr _ _ _ _ _ _ rfl hr,
   moment_congr _ _ _ _ _ _ rfl hl,moment_congr _ _ _ _ _ _ rfl hr]
private theorem jacPoly_ne (hd:2≤d) (hs :d*s≤a) :jacPoly d s a≠0:= by
 classical
 let i₁:=jU hd hs
 let i₂:=KK d s a
 let w (i:I) :L:=if i = .inl i₁∨i = .inr i₂ then 1 else 0
 have hl (i:Slot d s a) (hi:i≠i₁) :w (.inl i)=0:= by simp [w,hi]
 have hr (i:Slot d s (a+s+1)) (hi:i≠i₂) :w (.inr i)=0:= by simp [w,hi]
 have hv :zIe w (jacPoly d s a) = -1 := by
   simp only [jacPoly,map_sub,map_mul,map_moment,zTw]
   rw [moment_single _ _ _ _ _ _ i₁ hl,moment_single _ _ _ _ _ _ i₂ hr,
     moment_single _ _ _ _ _ _ i₁ hl,moment_single _ _ _ _ _ _ i₂ hr]
   simp [w,i₁,i₂,jU,KK]
 intro h
 rw [h,map_zero] at hv
 exact neg_ne_zero.mpr one_ne_zero hv.symm
theorem proof :qG7TGJa.c2 := by
 intro d s a hd _ hs b c hc q
 have heval :=(replaced_independent q).eq_zero_of_aeval_eq_zero
 constructor
 · rw [← eval_jac q]
   exact fun h=>jacPoly_ne hd hs (heval _ h)
 · let y :Index d s a := .inr (constant d s (a+s+1))
   let T:jo d s a :=MvPolynomial.C b+MvPolynomial.C c*z9v y
   have ht:T≠0:= by
    intro h
    have h₀:=congrArg (zY9 (fun _:Index d s a=>(0:L))) h
    have h₁:=congrArg (zY9 (fun _:Index d s a=>(1 :L))) h
    have hb:b=0:= by simpa [T] using h₀
    exact hc (by simpa [T,hb] using h₁)
   have he :zIe (replaced q) T=gauge b c q.val.2 := by
    simp [T,y,qZu9hjc.gauge,replaced_y]
   rw [← he]
   exact fun h=>ht (heval _ h)
end
end qqgIGhd
end
