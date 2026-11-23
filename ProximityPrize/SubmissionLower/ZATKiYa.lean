import ProximityPrize.SubmissionLower.ZTbQzvb
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace qbjv5ec
noncomputable section
open Polynomial Finset
open P5 (K)
open cu (L FX jz)
open P5_7_7 (Dg phys embed seedDerivative nodeRate)
open qGnV2ac (EquationBounds Sections atPair)
def c1 :Prop :=
  ∀ (F:Dg) (l h:ℕ),EquationBounds F l h →
    ∀ x r :L,TameAt F x r
def c2 :Prop :=
  ∀ (F:Dg) (l h:ℕ),EquationBounds F l h →
    ∀ x r :L,TameAt F x r →
      ∃ (k :ℕ) (T:Coeff[X]),
        reciprocalResultant F r=C (C ((Polynomial.X (R:=L) - C x)^k))*T ∧
        (T.coeff 0).map (evalRingHom x)≠0
private theorem phys_inj:Function.Injective phys :=IsFractionRing.injective L[X] FX
private def aee (z :L) :Coeff →+* L[X] :=evalRingHom (C z)
private theorem cut_map {R E :Type*} [CommRing R] [CommRing E] (e :R[X] →+* E)
  (F G:R[X]) (r :R) :
  (cutOver F G r).map e =
    (polarOver F r).map (e.comp C)+C (e (Polynomial.X (R:=R)))*G.map (e.comp C) := by
 simp only [cutOver,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_map,map_C]
private theorem polar_degree {R:Type*} [CommRing R] (F:R[X]) (r :R)
  (hF:0<F.natDegree) : (polarOver F r).natDegree≤F.natDegree := by
 have hd:=natDegree_derivative_lt hF.ne'
 unfold polarOver
 exact natDegree_mul_le.trans ((Nat.add_le_add_right (natDegree_X_sub_C_le _) _).trans
  (by omega))
private theorem constant_resultant {R:Type*} [CommRing R] (F G:R[X]) (r :R) :
  (resultantOver F G r).coeff 0=F.resultant (polarOver F r) F.natDegree F.natDegree := by
 let e :R[X] →+* R:=constantCoeff
 have he :e.comp C=RingHom.id R:=RingHom.ext fun b=> by simp [e]
 have heX:e (Polynomial.X (R:=R))=0:=coeff_X_zero
 have hf : (F.map C).map e=F:= by rw [Polynomial.map_map,he,Polynomial.map_id]
 have hg: (cutOver F G r).map e=polarOver F r := by
  rw [cut_map,he,heX,C_0,zero_mul,add_zero,Polynomial.map_id]
 change e (resultantOver F G r)= _
 unfold resultantOver
 rw [← resultant_map_map (F.map C) (cutOver F G r) _ _ e,hf,hg]
private theorem polar_height {F:Dg} {h:ℕ}
   (H : ∀ i,(F.coeff i).natDegree≤h) (r :L) (i:ℕ) :
   ((polar F r).coeff i).natDegree≤h:= by
 have hd (j:ℕ) : (F.derivative.coeff j).natDegree≤h:= by
   rw [coeff_derivative,← Nat.cast_succ,← C_eq_natCast]
   exact (natDegree_mul_C_le _ _).trans (H (j+1))
 rw [polar,polarOver,sub_mul (Polynomial.X (R:=Coeff)) (C (C (C r))) F.derivative,
   coeff_sub,coeff_C_mul]
 apply (natDegree_sub_le _ _).trans
 refine max_le ?_ ((natDegree_C_mul_le _ _).trans (hd i))
 cases i with
 | zero=>simp
 | succ i=>rw [coeff_X_mul]; exact hd i
private theorem constant_degree {F:Dg} {l h:ℕ}
   (H :EquationBounds F l h) (r :L) :
   ((reciprocalResultant F r).coeff 0).natDegree≤2*l*h:= by
 have hR: (reciprocalResultant F r).coeff 0 =
     F.resultant (polar F r) F.natDegree F.natDegree :=
   constant_resultant F (seedDerivative F) (C (C r))
 rw [hR,H.jU]
 classical
 let M:=F.sylvester (polar F r) l l
 have hentry (i j:Fin (l+l)) : (M i j).natDegree≤h:= by
   induction j using Fin.addCases with
   | left j =>
     simp only [M,sylvester,Matrix.of_apply,Fin.addCases_left]
     split
     · exact polar_height H.height r _
     · simp
   | right j =>
     simp only [M,sylvester,Matrix.of_apply,Fin.addCases_right]
     split
     · exact H.height _
     · simp
 change M.det.natDegree≤_
 rw [Matrix.det_apply]
 apply natDegree_sum_le_of_forall_le
 intro π _
 have hp: (∏ i,M (π i) i).natDegree≤2*l*h :=
   (natDegree_prod_le _ _).trans (calc
     _ ≤ ∑ _:Fin (l+l),h:=sum_le_sum fun i _=>hentry (π i) i
     _ = _:= by simp [two_mul,Nat.mul_comm])
 rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;> simpa [hh] using hp
private theorem bpF (G:Dg) (z :K) (P Q:L[X]) :
  G.eval₂ (phys.comp (aee (algebraMap K L z))) (phys P/phys Q)=atPair G z P Q:= by
 rw [atPair,embed,coe_mapRingHom,eval₂_map]
 congr 1
 apply RingHom.ext
 intro b
 change phys (b.eval (C (algebraMap K L z)))=(b.map phys).eval (jz z)
 rw [eval_map]
 exact (eval₂_hom (p:=b) phys (C (algebraMap K L z))).symm
private theorem c4s (F:Dg) (r :L) (z :K) (P Q:L[X]) :
  atPair (polar F r) z P Q=(phys P/phys Q - phys (C r))*atPair F.derivative z P Q:= by
 rw [← bpF (polar F r),← bpF F.derivative]
 simp [polar,polarOver,aee]
private theorem reciprocal_zero {E :Type*} [Field E] (a b p q r d v :E)
  (ha :a≠0) (hb:b≠0) (hq:q≠0) (hd:d≠0) (h:a/b = -(v/d)*q^2) :
  (p/q-r)*d+(b*q*(p-r*q)/a)*v=0:= by
 field_simp [ha,hb,hq,hd] at h ⊢
 linear_combination (p-r*q)*h
private theorem common_resultant {R E :Type*} [CommRing R] [CommRing E]
  (f g:R[X]) {m n:ℕ} (hf :f.natDegree≤ m) (hg:g.natDegree≤n)
  (hm:m≠0) (e :R →+* E) (y :E)
  (hfr :f.eval₂ e y=0) (hgr :g.eval₂ e y=0) :
  e (f.resultant g m n)=0:= by
 obtain ⟨a,b,_,_,he⟩:=exists_mul_add_mul_eq_C_resultant f g hf hg (Or.inl hm)
 have hv :=congrArg (eval₂RingHom e y) he
 simpa only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,hfr,hgr,zero_mul,zero_add]
  using hv.symm
private theorem resultant_at {R E :Type*} [CommRing R] [CommRing E]
   (F G:R[X]) (r :R) (c:R →+* E) (y u:E)
   (hl:0<F.natDegree) (hd:G.natDegree≤F.natDegree)
   (hF:F.eval₂ c y=0)
   (hG: (polarOver F r).eval₂ c y+u*G.eval₂ c y=0) :
   (resultantOver F G r).eval₂ c u=0:= by
 let e :R[X] →+* E :=eval₂RingHom c u
 have he :e.comp C=c:=eval₂RingHom_comp_C c u
 have heX:e (Polynomial.X (R:=R))=u:=eval₂_X c u
 have hf : (F.map C).eval₂ e y=0:= by rwa [eval₂_map,he]
 have hg: (cutOver F G r).eval₂ e y=0:= by
   simpa only [cutOver,eval₂_add,eval₂_mul,eval₂_C,eval₂_map,he,heX] using hG
 have hc: (cutOver F G r).natDegree≤F.natDegree :=
   (natDegree_add_le _ _).trans (max_le (natDegree_map_le.trans (polar_degree F r hl))
     ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hd)))
 change e ((F.map C).resultant (cutOver F G r) F.natDegree F.natDegree)=0
 exact common_resultant (R:=R[X]) (E :=E) (F.map C) (cutOver F G r)
   (m:=F.natDegree) (n:=F.natDegree) natDegree_map_le hc hl.ne' e y hf hg
private theorem eval_resultant {F:Dg} {l h:ℕ}
   (H :EquationBounds F l h) (S:Sections F) {γ:K} (hγ:γ∈S.CF) (r :L) :
   (reciprocalResultant F r).eval₂ (phys.comp (aee (algebraMap K L (S.seed γ))))
     (phys (S.B γ*S.Q γ*(S.P γ - C r*S.Q γ))/phys (S.A γ))=0:= by
 let c:=phys.comp (aee (algebraMap K L (S.seed γ)))
 let y :=phys (S.P γ)/phys (S.Q γ)
 let u:=phys (S.B γ*S.Q γ*(S.P γ - C r*S.Q γ))/phys (S.A γ)
 have hm (G:Dg) :G.eval₂ c y=atPair G (S.seed γ) (S.P γ) (S.Q γ) :=
   bpF G _ _ _
 have hf :F.eval₂ c y=0:=(hm F).trans (S.root γ hγ)
 have hA:=(map_ne_zero_iff phys phys_inj).mpr (S.nonzero γ hγ)
 have hB:=(map_ne_zero_iff phys phys_inj).mpr (S.pole_denominator γ hγ)
 have hQ:=(map_ne_zero_iff phys phys_inj).mpr (S.denominator γ hγ)
 have hg: (polar F r).eval₂ c y+u*(seedDerivative F).eval₂ c y=0:= by
   rw [hm (polar F r),hm (seedDerivative F),c4s]
   simpa only [u,map_mul,map_sub] using reciprocal_zero _ _ (phys (S.P γ)) _
     (phys (C r)) _ _ hA hB hQ (S.simple γ hγ) (S.formula γ hγ)
 have hl:0<F.natDegree := by rw [H.jU]; have :=H.two_le; omega
 have hd: (seedDerivative F).natDegree≤F.natDegree := by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro i hi
   rw [qGnV2ac.coeff_seedDerivative,coeff_eq_zero_of_natDegree_lt hi,derivative_zero]
 exact resultant_at F (seedDerivative F) (C (C r)) c y u hl hd hf hg
private theorem eval_at_zero (T:L[X][X]) (x :L) (q A:L[X])
   (hA:A.eval x≠0) (hq:q.eval x=0)
   (h:T.eval₂ phys (phys q/phys A)=0) :
   (T.coeff 0).eval x=0:= by
 let d:=T.natDegree
 let N :L[X] := ∑ i∈range (d+1),T.coeff i*q^i*A^(d-i)
 have ha :phys A≠0:=(map_ne_zero_iff phys phys_inj).mpr (fun h0=>hA (by simp [h0]))
 have hN :phys N=T.eval₂ phys (phys q/phys A)*phys A^d:= by
   rw [eval₂_eq_sum_range,sum_mul]
   simp only [N,map_sum,map_mul,map_pow]
   refine sum_congr rfl (fun i hi => ?_)
   have he :d=i+(d-i) :=(Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hi))).symm
   rw [show phys A^d=phys A^i*phys A^(d-i) by rw [← pow_add,← he],
     div_pow,mul_assoc _ (_/_) _,← mul_assoc (_/_) _ _,
     div_mul_cancel₀ _ (pow_ne_zero _ ha),mul_assoc]
 have hv :N.eval x=0:= by
   rw [h,zero_mul] at hN
   simp [phys_inj (hN.trans (map_zero phys).symm)]
 simp only [N,eval_finsetSum,eval_mul,eval_pow,hq] at hv
 rw [sum_eq_single 0] at hv
 · simp only [pow_zero,mul_one,Nat.sub_zero] at hv
   exact (mul_eq_zero.mp hv).resolve_right (pow_ne_zero _ hA)
 · intro i _ hi
   simp [zero_pow hi]
 · simp
private theorem bound (norm:c2) (tame :c1) {F:Dg} {l h:ℕ}
    (H :EquationBounds F l h) (S:Sections F) (x r :L) (U:Finset K)
    (hU:U⊆S.CF) (hA : ∀ γ∈U,(S.A γ).eval x≠0)
    (hq : ∀ γ∈U,(S.B γ*S.Q γ*(S.P γ - C r*S.Q γ)).eval x=0) :
    U.card≤2*l*h:= by
  classical
  obtain ⟨k,T,hT,hn⟩:=norm F l h H x r (tame F l h H x r)
  let R:=(T.coeff 0).map (evalRingHom x)
  have hxk : (Polynomial.X (R:=L) - C x)^k≠0:=pow_ne_zero _ (X_sub_C_ne_zero x)
  have hd:R.natDegree≤2*l*h:= by
    have hh:=constant_degree H r
    rw [hT,coeff_C_mul,natDegree_C_mul hxk] at hh
    exact natDegree_map_le.trans hh
  have hr (γ:K) (hγ:γ∈U) :R.eval (algebraMap K L (S.seed γ))=0:= by
    let q:=S.B γ*S.Q γ*(S.P γ - C r*S.Q γ)
    let z :=algebraMap K L (S.seed γ)
    have he :=eval_resultant H S (hU hγ) r
    rw [hT,eval₂_mul,eval₂_C] at he
    have hnz : (phys.comp (aee z)) (C ((Polynomial.X (R:=L) - C x)^k))≠0:= by
      change phys ((C ((Polynomial.X (R:=L) - C x)^k) :Coeff).eval (C z))≠0
      rw [eval_C]
      exact (map_ne_zero_iff phys phys_inj).mpr hxk
    have hv :=(mul_eq_zero.mp he).resolve_left hnz
    have ht: (T.map (aee z)).eval₂ phys (phys q/phys (S.A γ))=0:= by
      rwa [eval₂_map]
    have hx :=eval_at_zero _ x q _ (hA γ hγ) (hq γ hγ) ht
    change ((T.coeff 0).map (evalRingHom x)).eval z=0
    rw [eval_map]
    simpa only [coe_evalRingHom,eval_C] using
      (eval₂_hom (p:=T.coeff 0) (evalRingHom x) (C z)).trans
        (by simpa only [coeff_map,aee,coe_evalRingHom] using hx)
  refine (le_trans ?_ hd)
  rw [← card_image_of_injOn ((FaithfulSMul.algebraMap_injective K L).comp_injOn
    (S.injective.mono hU))]
  apply card_le_degree_of_subset_roots
  intro z hz
  obtain ⟨γ,hγ,rfl⟩:=mem_image.mp (Finset.mem_def.mpr hz)
  exact (mem_roots hn).mpr (hr γ hγ)
theorem of_children (tame :c1) (norm:c2) :qGnV2ac.c1 := by
 classical
 intro F l h H S x a b hab
 let U:=S.CF.filter fun γ =>
   (S.P γ).eval x*a=(S.Q γ).eval x*b∧(S.A γ).eval x≠0
 have hA (γ:K) (hγ:γ∈U) : (S.A γ).eval x≠0:=(mem_filter.mp hγ).2.2
 have hU:U⊆S.CF:=filter_subset _ _
 have hle :2*l*h≤nodeRate l*h:=Nat.mul_le_mul_right _ (by unfold nodeRate; omega)
 by_cases ha :a=0
 · refine (bound norm tame H S x 0 U hU hA (fun γ hγ => ?_)).trans hle
   have hb:=hab.resolve_left (fun hv=>hv ha)
   have he :=(mem_filter.mp hγ).2.1
   rw [ha,mul_zero] at he
   have hq:=(mul_eq_zero.mp he.symm).resolve_right hb
   simp [hq]
 · refine (bound norm tame H S x (b/a) U hU hA (fun γ hγ => ?_)).trans hle
   have he :=(mem_filter.mp hγ).2.1
   have hh: (b/a)*(S.Q γ).eval x=(S.P γ).eval x := by
     apply (mul_right_cancel₀ ha)
     rw [mul_comm (b/a),mul_assoc,div_mul_cancel₀ _ ha,he]
   simp [hh]
end
end qbjv5ec
end
section
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace q7kdBxd
noncomputable section
open Polynomial Finset


open qGnV2ac (Sections)
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ (J:Input) (S:Sections J.F),∃ (G:Input) (T:Sections G.F),
    G.l=J.l∧G.h=J.h∧G.s=J.s∧G.b=J.b ∧
      intrinsic S J.s≤finitePoles T
private theorem budgets (l u s L₀ W:ℕ) (hl:2≤l) (hL:2*u+s=L₀)
   (hW:l*L₀≤W) :
   let b:=W-l*u-l*s
   b+l*s=W-l*u ∧
   (2*l-2)*b+l*(l-1)*s=(2*l-2)*W-l*(l-1)*L₀ ∧
   (6*l-4)*b+(3*l*l-2)*s≤(6*l-4)*W-(3*l*l-4*l+2)*L₀:= by
 let b:=W-l*u-l*s
 change b+l*s=W-l*u ∧
   (2*l-2)*b+l*(l-1)*s=(2*l-2)*W-l*(l-1)*L₀ ∧
   (6*l-4)*b+(3*l*l-2)*s≤(6*l-4)*W-(3*l*l-4*l+2)*L₀
 have hw' : l*u+l*s≤W:= by
   rw [← mul_add]
   exact (Nat.mul_le_mul_left _ (by omega :u+s≤L₀)).trans hW
 have heW:b+l*u+l*s=W:= by
   dsimp [b]
   omega
 have hb:b+l*s=W-l*u:= by omega
 refine ⟨hb,?_,?_⟩
 · have h₁:2≤2*l:= by omega
   have h₂:1≤l:= by omega
   have he : (2*l-2)*b+l*(l-1)*s+l*(l-1)*L₀=(2*l-2)*W:= by
     zify [h₁,h₂] at hL heW ⊢
     linear_combination (2*(l:ℤ)-2)*heW-(l:ℤ)*((l:ℤ)-1)*hL
   omega
 · have h₁:4≤6*l:= by omega
   have h₃:4*l≤3*l*l:=Nat.mul_le_mul_right l (by omega)
   have h₂:2≤3*l*l:=(by omega :2≤4*l).trans h₃
   have he : (6*l-4)*b+(3*l*l-2)*s+(3*l*l-4*l+2)*L₀+(4*l-4)*u=(6*l-4)*W:= by
     have h₄:4≤4*l:= by omega
     zify [h₁,h₂,h₃,h₄] at hL heW ⊢
     linear_combination (6*(l:ℤ)-4)*heW-(3*(l:ℤ)^2-4*(l:ℤ)+2)*hL
   omega
end
end q7kdBxd
end
