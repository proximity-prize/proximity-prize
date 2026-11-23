import ProximityPrize.SubmissionLower.ZgN8mRc
import ProximityPrize.SubmissionLower.ZRSdJhe
import ProximityPrize.SubmissionLower.ZAsXn9b
set_option Elab.async false
open _root_ renaming CommRing → za6, Finset.mul_sum → zxw, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Function.Injective → zq4, Ideal.Quotient.mk → zVv, Ideal.span → zye, IsFractionRing.injective → zxb, LinearEquiv.ofInjective → zjT, LinearMap.toMatrix → z2F, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.totalDegree_finsetSum_le → zTw, MvPolynomial.totalDegree_mul → zhM, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.coe_mapRingHom → zKC, Polynomial.commRing → zqU, Polynomial.mapRingHom → zhd, Polynomial.map_ne_zero_iff → zeI, Polynomial.monomial → zdM, PowerSeries.constantCoeff → zbO
section
section
set_option autoImplicit true
namespace K1_14_3_4_5
noncomputable section
open Polynomial
open scoped BigOperators
theorem matrix_finrank {F:Type*} [Field F] {n:ℕ}
   (M:Matrix (Fin n) (Fin n) (zM1 F)) (hM:M.det≠0) :
   FiniteDimensional F (MatrixQuot M) ∧
     zsE F (MatrixQuot M)=M.det.natDegree := by
 classical
 let R:=zM1 F
 let V:=Fin n→R
 let f :V →ₗ[R] V:=M.toLin'
 let N :=LinearMap.range f
 have hf :zq4 f := by
   intro x y hxy
   apply M.mulVec_injective_of_det_ne_zero hM
   change M.mulVec x=M.mulVec y at hxy
   exact hxy
 let b:=Pi.basisFun R (Fin n)
 have hN :zsE R N=zsE R V:=LinearMap.finrank_range_of_inj hf
 let a :=Submodule.smithNormalFormCoeffs b hN
 have ha (i:Fin n) :a i≠0:=Submodule.smithNormalFormCoeffs_ne_zero b hN i
 have (i:Fin n) :zAa F (R ⧸ zye ({a i} : Set R)) :=
   Module.Finite.of_basis (AdjoinRoot.powerBasis (ha i)).basis
 let eq :=(N.quotientEquivPiSpan b hN).restrictScalars F
 refine ⟨FiniteDimensional.of_injective eq.toLinearMap eq.injective,?_⟩
 have hdim:zsE F (MatrixQuot M) = ∑ i,(a i).natDegree := by
   change zsE F (V ⧸ N)= _
   rw [Submodule.finrank_quotient_eq_sum F b hN]
   exact zUo rfl fun i _=>finrank_quotient_span_eq_natDegree (f :=a i)
 let top:=Submodule.smithNormalFormTopBasis b hN
 let bot:=Submodule.smithNormalFormBotBasis b hN
 let source :=bot.map (zjT f hf).symm
 let e :V ≃ₗ[R] V:=top.equiv source (Equiv.refl _)
 have he (i:Fin n) :f (e (top i))=(bot i:V) := by
   change f ((top.equiv source (Equiv.refl _)) (top i))= _
   rw [Module.Basis.equiv_apply]
   change f ((zjT f hf).symm (bot i))= _
   exact congrArg Subtype.val ((zjT f hf).apply_symm_apply (bot i))
 have hdiag:z2F top top (f.comp e.toLinearMap)=Matrix.diagonal a := by
   apply Matrix.ext
   intro i j
   rw [LinearMap.toMatrix_apply]
   change top.repr (f (e (top j))) i= _
   rw [he,Submodule.smithNormalFormBotBasis_def]
   by_cases hEq:i=j
   · subst j
     simp [top,a]
   · simp [top,a,hEq]
 have hdet: (∏ i,a i)=M.det*LinearMap.det e.toLinearMap:= by
   have h:=congrArg Matrix.det hdiag
   rw [LinearMap.det_toMatrix,LinearMap.det_comp,Matrix.det_diagonal] at h
   simpa [f] using h.symm
 rw [hdim,← natDegree_prod Finset.univ a (fun i _=>ha i),hdet,
   natDegree_mul hM e.isUnit_det'.ne_zero,natDegree_eq_zero_of_isUnit e.isUnit_det',add_zero]
end
end K1_14_3_4_5
end
section
namespace q9bKVmc
noncomputable section
open Polynomial
open qYVN5fe (lK pairQuot)
open K1_14_3_4_5 (MatrixQuot matrix_finrank)
private theorem monic_in_pair {K:Type} [Field K]
   (F G:lK K) {m n:ℕ} (hm:F.natDegree≤ m) (hn:G.natDegree≤n)
   (hc:IsCoprime (F.coeff m) (G.coeff n)) :
   ∃ H∈zye ({F,G} : Set (lK K)),H.Monic∧H.natDegree=max m n:= by
 obtain ⟨a,b,hab⟩:=hc
 let k :=max m n
 have hmk :m≤k :=le_max_left _ _
 have hnk :n≤k :=le_max_right _ _
 let H :=z1z a*(F*z7y ^(k - m)) +
   z1z b*(G*z7y ^(k - n))
 have hd (P:lK K) (c:zM1 K) {j:ℕ} (hj:P.natDegree≤j) (hjk :j≤k) :
     (z1z c*(P*z7y ^(k - j))).natDegree≤k :=
   (natDegree_C_mul_le _ _).trans <|
     (natDegree_mul_le_of_le hj (natDegree_X_pow_le _)).trans (by omega)
 have htop (P:lK K) {j:ℕ} (hjk :j≤k) :
     (P*z7y ^(k - j)).coeff k=P.coeff j:= by
   rw [coeff_mul_X_pow',ite_eq_left (by omega :k - j≤k),show k-(k - j)=j by omega]
 have hcoeff :H.coeff k=1 := by
   simpa only [H,coeff_add,coeff_C_mul,htop F hmk,htop G hnk] using hab
 have hdeg:H.natDegree=k :=
   eq_natDegree_of_le_mem_support
     ((natDegree_add_le _ _).trans (max_le (hd F a hm hmk) (hd G b hn hnk)))
     (mem_support_iff.mpr (hcoeff ▸ one_ne_zero))
 refine ⟨H,Ideal.mem_span_pair.mpr ⟨z1z a*z7y ^(k - m),
   z1z b*z7y ^(k - n),by dsimp [H]; ac_rfl⟩,?_,hdeg⟩
 rw [Monic,leadingCoeff,hdeg,hcoeff]
private theorem affine_surjection {K:Type} [Field K] (F G:lK K) {m n:ℕ}
    (hm:F.natDegree≤ m) (hn:G.natDegree≤n) (hk :max m n≤ m+n)
    (hc:IsCoprime (F.coeff m) (G.coeff n)) :
    ∃ f :MatrixQuot (F.sylvester G m n) →ₗ[K] pairQuot F G,Function.Surjective f := by
  let R:=zM1 K
  let M:=F.sylvester G m n
  let J:=LinearMap.range M.toLin'
  let I:=zye ({F,G} : Set (lK K))
  let q:=Ideal.Quotient.mkₐ R I
  let b₁:=degreeLT.basisProd R m n
  let b₂:=degreeLT.basis R (m+n)
  let T:=q.toLinearMap.comp (degreeLT R (m+n)).subtype
  let l:=T.comp b₂.equivFun.symm.toLinearMap
  have hJ:J≤LinearMap.ker l:= by
    rintro _ ⟨x,rfl⟩
    change T (b₂.equivFun.symm (M.toLin' x))=0
    have hcoords :M.toLin b₁ b₂ (b₁.equivFun.symm x) =
        b₂.equivFun.symm (M.toLin' x) := by
      rw [Matrix.toLin,z2F,LinearEquiv.trans_symm,LinearEquiv.trans_apply,
        LinearMap.toMatrix'_symm,LinearEquiv.arrowCongr_symm_apply,LinearEquiv.apply_symm_apply]
    have hM:M.toLin b₁ b₂=sylvesterMap F G hm hn :=
      (congrArg (Matrix.toLin b₁ b₂) (toMatrix_sylvesterMap' F G hm hn)).symm.trans
        (Matrix.toLin_toMatrix b₁ b₂ _)
    rw [← hcoords,hM]
    let pq:=b₁.equivFun.symm x
    change q (F*(pq.2 :lK K)+G*(pq.1 :lK K))=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_pair.mpr ⟨(pq.2 :lK K),(pq.1 :lK K),by ac_rfl⟩)
  refine ⟨(J.liftQ l hJ).restrictScalars K,?_⟩
  obtain ⟨H,hHI,hH,hdeg⟩:=monic_in_pair F G hm hn hc
  have hq:q H=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hHI
  intro y
  obtain ⟨v,rfl⟩:=Ideal.Quotient.mkₐ_surjective R I y
  have hs :v %ₘ H∈degreeLT R (m+n) := by
    apply mem_degreeLT.mpr
    refine (degree_modByMonic_lt _ hH).trans_le ?_
    rw [degree_eq_natDegree hH.ne_zero,hdeg]
    exact Nat.cast_le.mpr hk
  refine ⟨J.mkQ (b₂.equivFun ⟨v %ₘ H,hs⟩),?_⟩
  change T (b₂.equivFun.symm (b₂.equivFun ⟨v %ₘ H,hs⟩))=q v
  rw [LinearEquiv.symm_apply_apply]
  change q (v %ₘ H)=q v
  symm
  calc
    q v=q (v %ₘ H+H*(v /ₘ H)) :=congrArg q (modByMonic_add_div v H).symm
    _ = _:= by
      rw [map_add,map_mul,hq,zero_mul (q (v /ₘ H)),add_zero (q (v %ₘ H))]
theorem proof :qYVN5fe.c2 := by
 intro K _ F G m n _ _ hm hn hc hres
 obtain ⟨f,hf⟩:=affine_surjection F G hm hn (by omega) hc
 obtain ⟨hfinite,hdeg⟩:=matrix_finrank (F.sylvester G m n) hres
 let:zAa K (MatrixQuot (F.sylvester G m n)) :=hfinite
 exact ⟨Module.Finite.of_surjective f hf,
  (LinearMap.finrank_le_finrank_of_surjective hf).trans_eq hdeg⟩
end
end q9bKVmc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qNL8tLd
noncomputable section
open Polynomial
open scoped Classical
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index jo aMp)
open qpVvmab
private theorem finite_bad {R:Type} [za6 R] [IsDomain R]
   (k :L →+* R) {p:R[X]} (hp:p≠0) :
   {z :L | p.eval (k z)=0}.Finite :=
 (finite_setOfPred_isRoot hp).preimage k.injective.injOn
private def move {ι:Type} (u v :ι) (δ:ι→L) (z :L) (i:ι) :L :=
 δ i+(if i=u then z else 0)+(if i=v then z^2 else 0)
private def aoV {R:Type} [za6 R] (a b c:R) :R[X] :=
 C a+monomial 1 b+monomial 2 c
private theorem map_toggle {R:Type} [za6 R] (k :L →+* R)
  (p:Prop) [Decidable p] (z :L) :
  k (if p then z else 0)=if p then k z else 0:= by
 split <;> simp_all
variable {E :Type} [Field E] [Algebra L E]
private theorem finite_sample {d s W:ℕ} (α:Index d s W→E) (δ:Index d s W→L)
   (u v :Index d s W) (Q:jo d s W) (hQ:sample α δ Q≠0) :
   {z :L | sample α (move u v δ z) Q=0}.Finite := by
 let k :=algebraMap L E
 let p:E[X] := Q.eval₂ (C.comp k) (fun i =>
   aoV (α i+k (δ i)) (if i=u then 1 else 0) (if i=v then 1 else 0))
 have he (z :L) :p.eval (k z)=sample α (move u v δ z) Q:= by
   rw [← coe_evalRingHom]
   dsimp only [p]
   rw [MvPolynomial.eval₂_comp_left,sample]
   have hc: (evalRingHom (k z)).comp (C.comp k)=k := by
     ext a
     simp
   rw [hc]
   congr 1
   funext i
   change (aoV (α i+k (δ i)) (if i=u then 1 else 0) (if i=v then 1 else 0)).eval
     (k z)= α i+k (move u v δ z i)
   simp only [aoV,move,eval_add,eval_C,eval_monomial,pow_one,ite_mul,one_mul,
     zero_mul,map_add,map_toggle,map_pow,add_assoc]
   split_ifs <;> rfl
 have h0:move u v δ 0=δ:= by
   funext i
   simp [move]
 have hp:p≠0:= by
   intro hz
   apply hQ
   have he₀:=he 0
   rw [hz,eval_zero,h0] at he₀
   exact he₀.symm
 exact (finite_bad k hp).subset fun z hz=>(he z).trans hz
private theorem sum_slot {R:Type} [za6 R] {d s W:ℕ}
   (j:Slot d s W) (a x y :R) :
   (∑ i:Slot d s W,(if i=j then a else 0)*x^i.val.2.val*y^i.val.1.val) =
     a*x^j.val.2.val*y^j.val.1.val := by
 rw [zi6 j]
 · simp
 · intro i _ hi
   simp [hi]
 · simp
private theorem block_move {R:Type} [za6 R] {d s W:ℕ}
    (f :Slot d s W→R) (j k :Slot d s W) (a b x y :R) :
    aMp (fun i=>f i+(if i=j then a else 0)+(if i=k then b else 0)) x y =
      aMp f x y+a*x^j.val.2.val*y^j.val.1.val +
        b*x^k.val.2.val*y^k.val.1.val := by
  simp only [aMp,add_mul,Finset.sum_add_distrib,sum_slot]
private theorem quad_sep {R ι:Type} [za6 R] [IsDomain R]
  (a x y :ι→R) {i j:ι} (t:R) (ht:t≠0)
  (hne : (x i,y i)≠(x j,y j)) :
  aoV (a i) (x i*t) (y i*t)-aoV (a j) (x j*t) (y j*t)≠0:= by
 intro hz
 have h:=sub_eq_zero.mp hz
 have hx :=congrArg (fun p:R[X]=>p.coeff 1) h
 have hy :=congrArg (fun p:R[X]=>p.coeff 2) h
 simp [aoV,coeff_monomial,ht] at hx hy
 exact hne (Prod.ext hx hy)
theorem proof :qpVvmab.c2 := by
  intro E _ _ A hs hd B δ U Q hQ
  let W:=A.b+A.d*A.s
  have hW:A.s≤W-A.s := by
    have hh:=Nat.mul_le_mul_right A.s hd
    change 2*A.s≤A.d*A.s at hh
    dsimp [W]
    omega
  let j:Slot (A.d-1) A.s (W-A.s) :=
    ⟨(0,⟨1,by omega⟩),by simpa using (Nat.succ_le_of_lt hs).trans hW⟩
  let k :Slot (A.d-1) A.s (W-A.s) :=⟨(⟨1,by omega⟩,0),by simpa using hW⟩
  let u:Index A.d A.s W := .inr (.inr j)
  let v :Index A.d A.s W := .inr (.inr k)
  let f :=value A B δ δ U
  let ε:Series E :=PowerSeries.X
  let P (i:Fin B.size) : (Series E)[X] :=aoV (f i) (U.x i* ε) (U.y i* ε)
  let K:=algebraMap L (Series E)
  have hP (z :L) (i:Fin B.size) :
      (P i).eval (K z)=value A B δ (move u v δ z) U i:= by
    have hb (l:Slot (A.d-1) A.s (W-A.s)) :
        base (actual A B) (move u v δ z) (.inr (.inr l)) =
          base (actual A B) δ (.inr (.inr l)) +
            (if l=j then K z* ε else 0)+(if l=k then K z^2* ε else 0) := by
      simp only [base,move,u,v,Sum.inr.injEq,map_add,map_toggle,map_pow,
        add_mul,ite_mul,zero_mul,K,ε,add_assoc]
    simp only [P,aoV,eval_add,eval_C,eval_monomial,pow_one,value,hb,block_move]
    simp [j,k,f,value]
    ring
  let I := {ij:Fin B.size×Fin B.size // ij.1≠ij.2}
  let D (ij:I) :=P ij.val.1-P ij.val.2
  have hD (ij:I) :D ij≠0:= by
    have hne : (U.x ij.val.1,U.y ij.val.1)≠(U.x ij.val.2,U.y ij.val.2) := by
      intro he
      apply ij.property
      apply B.distinct
      exact Prod.ext ((U.x₀ _).symm.trans
        ((congrArg (fun p=>zbO p.1) he).trans (U.x₀ _)))
        ((U.y₀ _).symm.trans
        ((congrArg (fun p=>zbO p.2) he).trans (U.y₀ _)))
    exact quad_sep f U.x U.y ε PowerSeries.X_ne_zero hne
  obtain ⟨z,hz⟩:=((finite_sample (actual A B) δ u v Q hQ).union
    (Set.finite_iUnion fun ij:I=>finite_bad K (hD ij))).exists_notMem
  refine ⟨move u v δ z,?_,?_,fun h=>hz (Or.inl h),?_⟩
  · intro l
    simp [move,u,v]
  · intro l
    simp [move,u,v]
  · intro i l h
    by_contra hn
    let ij:I:=⟨(i,l),hn⟩
    apply hz
    apply Or.inr
    refine Set.mem_iUnion.mpr ⟨ij,?_⟩
    change (D ij).eval (K z)=0
    simp only [D,ij,eval_sub,hP,h,sub_self]
end
end qNL8tLd
end
section
namespace qoGY3we
noncomputable section
open Polynomial
open cu (L)
open qrezXJe (rootEval tangentDenom tangentValue)
open q2TwyLa (i5 diffPoly)
open scoped WithZero
def c1 :Prop :=TameLog
def c2 :Prop :=
  TameLog → ∀ (A:Cover) (P:L[X]) (J:LocalRoot A.f A.r P),
    (bY false).IsIntegralElem (bY false A.g*J.logSeed) ∧
    (bY false).IsIntegralElem
      (bY false A.g.derivative*J.logSeed - bY false (diffPoly A.g)*J.logPhys)
def c3:Prop :=
  TameLog → ∀ (A:Cover) (P:L[X]) (J:LocalRoot A.f A.r P) (j:Away A →+* Series),
    j.comp (algebraMap i5[X] (Away A))=bY true→j.IsIntegralElem J.logSeed
theorem of_children (tame :c1) (finite :c2) (infinity :c3) :
   qrezXJe.c1 := by
 intro E _ _ f D r G w a P _ _ hp hd hv hf hg hn hl hs hgD hpow hdeg hu hP hroot
 obtain ⟨A,_,hf0,hf1,hG⟩:=cover a f r G
   (fun i j=> by simpa [← hv] using hf i j)
   (fun j=> by simpa [← hv] using hg j)
   hp hd hn hl hs hgD hpow hdeg ((hv _).symm.trans hu)
 have hroot' : rootEval (A.f.map reduce) P=0:=hf0.symm ▸ hroot
 obtain ⟨hsimple,href⟩:=mark_guards A P hroot'
 obtain ⟨J⟩:=local_root A.f A.r P hroot' hsimple href
 have he :seedTangent A.f P=tangentValue a f P:= by
   simp only [seedTangent,tangentValue,tangentDenom,hf0,hf1]
 obtain ⟨N,B,hB,hcop,hform⟩:=q1kuFjb.reduced_pair (seedTangent A.f P)
 obtain ⟨h₁,h₂⟩:=finite tame A P J
 obtain ⟨j,hj⟩:=awayChart A
 refine ⟨⟨?_,N,B,hB,hcop,hform.trans he,?_,?_⟩⟩
 · simpa only [tangentDenom,hf0] using hsimple
 · simpa only [hG] using finite_den A J hB hcop hform h₁ h₂
 · exact aNb A J j hj (infinity tame A P J j hj) hP href hB hform
end
end qoGY3we
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qFBRuya
noncomputable section
open Polynomial Finset
open cu (L)
open qAW6lac (Index block)
open qYVN5fe
open private cap_valid form_weight from ProximityPrize.SubmissionLower.ZgN8mRc
private theorem slot_exists {d s W x y :ℕ} {j:Fin 3}
   (hy :y≤yCap d j) (hxy :x+y*s≤wCap s W j) :
   ∃ a :Index d s W,block a=j∧yDeg a=y∧xDeg a=x := by
 fin_cases j <;> simp [yCap,wCap] at hy hxy
 · exact ⟨.inl ⟨(⟨y,by omega⟩,⟨x,by omega⟩),hxy⟩,rfl,rfl,rfl⟩
 · exact ⟨.inr (.inl ⟨(⟨y,by omega⟩,⟨x,by omega⟩),hxy⟩),rfl,rfl,rfl⟩
 · exact ⟨.inr (.inr ⟨(⟨y,by omega⟩,⟨x,by omega⟩),hxy⟩),rfl,rfl,rfl⟩
private def Lw {d s W:ℕ} (k :Fin 3) (i:Index d s W) :FixedRing d s W k :=
 if h:block i=k then 0 else z9v ⟨i,h⟩
private abbrev raw (d s W:ℕ) (k j:Fin 3) :lK (FixedRing d s W k) :=
 form (Lw k) j
private theorem pair_eq (d s W:ℕ) (k j:Fin 3) :
   pairForm d s W k j=(raw d s W k j).map
     (mapRingHom (algebraMap (FixedRing d s W k) (Ground d s W k))) := by
 rw [form_map,pairForm]
 congr 1
 funext i
 by_cases hi:block i=k <;> simp [Lw,fixedVars,hi]
private def specialize {d s W:ℕ} (k :Fin 3) (a b:Index d s W) :
  FixedRing d s W k →+* L :=
 zY9 (fun i=>if i.val=a∨i.val=b then 1 else 0)
private theorem specialize_form {d s W:ℕ} {k :Fin 3} {a b:Index d s W}
   (ha :block a≠k) (hb:block b=block a→b=a) :
   (raw d s W k (block a)).map (mapRingHom (specialize k a b)) =
     monomial (yDeg a) (monomial (xDeg a) (1 :L)) := by
 classical
 rw [form_map,form,zi6 a]
 · simp [Lw,specialize,ha]
 · intro i _ hia
   by_cases hi:block i=block a
   · have hib:i≠b:= fun e=>hia (e.trans (hb (e ▸ hi)))
     simp [Lw,specialize,hi,ha,hia,hib]
   · simp [hi]
 · simp
private theorem top_slot {d s W:ℕ} (hW:d*s≤W) (j:Fin 3) :
  ∃ a :Index d s W,block a=j∧yDeg a=yCap d j ∧
    xDeg a=wCap s W j - yCap d j*s :=
 slot_exists le_rfl (by rw [Nat.sub_add_cancel (cap_valid hW j)])
private theorem map_coefficient {A B:Type} [za6 A] [za6 B]
   (f :A →+* B) (F:lK A) (m:ℕ) :
   (F.coeff m).map f=(F.map (mapRingHom f)).coeff m :=
 (coeff_map (p:=F) (mapRingHom f) m).symm
private theorem top_degree {d s W:ℕ} {k j:Fin 3} (hk :j≠k) (hW:d*s≤W)
   {a :Index d s W} (ha :block a=j) (hy :yDeg a=yCap d j)
   (hx :xDeg a=wCap s W j - yCap d j*s) :
   ((raw d s W k j).coeff (yCap d j)).natDegree=xDeg a ∧
     (raw d s W k j).coeff (yCap d j)≠0:= by
 let f :=(raw d s W k j).coeff (yCap d j)
 have hf :f.map (specialize k a a)=monomial (xDeg a) 1 := by
   have he :=specialize_form (ha.trans_ne hk) (fun _=>rfl :block a=block a→a=a)
   rw [ha,hy] at he
   dsimp only [f]
   rw [map_coefficient,he,coeff_monomial_same]
 have hz :f≠0:= by
   intro h
   rw [h,Polynomial.map_zero] at hf
   exact one_ne_zero ((monomial_eq_zero_iff _ _).mp hf.symm)
 have hl:xDeg a≤f.natDegree := by
   have hm:=natDegree_map_le (p:=f) (f :=specialize k a a)
   rwa [hf,natDegree_monomial_eq _ one_ne_zero] at hm
 have hu:f.natDegree≤xDeg a := by
   have hw:=form_weight (Lw k) j (cap_valid hW j) (yCap d j) hz
   change f.natDegree+s*yCap d j≤wCap s W j at hw
   rw [Nat.mul_comm s] at hw
   rw [hx]
   omega
 exact ⟨le_antisymm hu hl,hz⟩
private theorem resultant_of_specialization {A B:Type} [za6 A] [za6 B] [Nontrivial B]
  (ϕ:A →+* B) {f g:zM1 A} {m n:ℕ}
  (hf : (f.map ϕ).coeff m=1) (hg:g.map ϕ=1) :f.resultant g m n≠0:= by
 intro h
 have h' := (resultant_map_map f g m n ϕ).trans (show ϕ (f.resultant g m n)=0 by
  rw [h,map_zero])
 rw [hg,resultant_one_right,hf,one_pow] at h'
 exact one_ne_zero h'
private theorem specialize_pair {d s W:ℕ} {k j l:Fin 3}
    (hj:j≠k) (hl:l≠k) (hjl:j≠l)
    {a b:Index d s W} (ha :block a=j) (hb:block b=l) :
    (raw d s W k j).map (mapRingHom (specialize k a b)) =
        monomial (yDeg a) (monomial (xDeg a) (1 :L)) ∧
    (raw d s W k l).map (mapRingHom (specialize k a b)) =
        monomial (yDeg b) (monomial (xDeg b) (1 :L)) := by
  constructor
  · have h:block b=block a→b=a := fun h =>
      (hjl (ha.symm.trans (h.symm.trans hb))).elim
    simpa only [ha] using specialize_form (ha.trans_ne hj) h
  · have h:block a=block b→a=b:= fun h =>
      (hjl (ha.symm.trans (h.trans hb))).elim
    have hs :specialize k b a=specialize k a b:= by simp only [specialize,or_comm]
    simpa only [hb,hs] using specialize_form (hb.trans_ne hl) h
private theorem mapped_coprime {R K:Type} [za6 R] [Field K]
  (ι:R →+* K) (hi:zq4 ι) {f g:zM1 R} {a b:ℕ}
  (hf :f.natDegree=a) (hg:g.natDegree=b) (hf0:f≠0)
  (hr :f.resultant g a b≠0) :IsCoprime (f.map ι) (g.map ι) := by
 by_contra hn
 have hz : (f.map ι).resultant (g.map ι)=0 :=
  resultant_eq_zero_iff.mpr ⟨Or.inl ((zeI hi).mpr hf0),hn⟩
 rw [natDegree_map_eq_of_injective hi,natDegree_map_eq_of_injective hi,hf,hg,
  resultant_map_map] at hz
 exact (map_ne_zero_iff ι hi).mpr hr hz
private theorem top_coprime {d s W:ℕ} {k j l:Fin 3} (hW:d*s≤W)
   (hj:j≠k) (hl:l≠k) (hjl:j≠l) :
   IsCoprime ((pairForm d s W k j).coeff (yCap d j)) ((pairForm d s W k l).coeff (yCap d l)) := by
 let m:=yCap d j
 let n:=yCap d l
 let F:=raw d s W k j
 let G:=raw d s W k l
 obtain ⟨a,ha,hay,hax⟩:=top_slot hW j
 obtain ⟨b,hb,hby,hbx⟩:=top_slot hW l
 obtain ⟨c,hc,hcy,hcx⟩:=slot_exists (d:=d) (s :=s) (W:=W) (j:=l) (x :=0) (y :=n)
   le_rfl (by simpa only [zero_add] using cap_valid hW l)
 obtain ⟨hF,hG⟩:=specialize_pair hj hl hjl ha hc
 have hr : (F.coeff m).resultant (G.coeff n) (xDeg a) (xDeg b)≠0:= by
   apply resultant_of_specialization (specialize k a c)
   · rw [map_coefficient,hF,hay,coeff_monomial_same,coeff_monomial_same]
   · rw [map_coefficient,hG,hcy,hcx,coeff_monomial_same]
     simp [monomial_zero_left]
 obtain ⟨hf,hf0⟩:=top_degree hj hW ha hay hax
 obtain ⟨hg,_⟩:=top_degree hl hW hb hby hbx
 rw [pair_eq d s W k j,pair_eq d s W k l,← map_coefficient,← map_coefficient]
 exact mapped_coprime _ (zxb (FixedRing d s W k) (Ground d s W k))
   hf hg hf0 hr
private theorem ordinate_resultant {d s W:ℕ} {k j l:Fin 3} (hW:d*s≤W)
   (hj:j≠k) (hl:l≠k) (hjl:j≠l) :
   (pairForm d s W k j).resultant (pairForm d s W k l) (yCap d j) (yCap d l)≠0:= by
 let F:=raw d s W k j
 let G:=raw d s W k l
 obtain ⟨a,ha,hay,hax⟩:=slot_exists (d:=d) (s :=s) (W:=W) (j:=j) (x :=0) (y :=yCap d j)
   le_rfl (by simpa only [zero_add] using cap_valid hW j)
 obtain ⟨b,hb,hby,hbx⟩:=slot_exists (d:=d) (s :=s) (W:=W) (j:=l) (x :=0) (y :=0)
   (Nat.zero_le _) (by simp)
 obtain ⟨hF,hG⟩:=specialize_pair hj hl hjl ha hb
 have hr :F.resultant G (yCap d j) (yCap d l)≠0:= by
   apply resultant_of_specialization (mapRingHom (specialize k a b))
   · rw [hF,hay,hax,coeff_monomial_same]
     simp [monomial_zero_left]
   · rw [hG,hby,hbx]
     simp [monomial_zero_left]
 rw [pair_eq d s W k j,pair_eq d s W k l,resultant_map_map]
 exact (zeI (zxb (FixedRing d s W k) (Ground d s W k))).mpr hr
private theorem other_blocks (k :Fin 3) :left k≠k∧right k≠k∧left k≠right k := by
 fin_cases k <;> decide
theorem proof :qYVN5fe.c1 := by
 intro d s W _ _ _ _ hW k
 obtain ⟨hj,hl,hjl⟩:=other_blocks k
 exact ⟨top_coprime hW hj hl hjl,ordinate_resultant hW hj hl hjl⟩
end
end qFBRuya
end
section
set_option backward.isDefEq.respectTransparency false
namespace qrtGZca
noncomputable section
open Polynomial Finset Matrix Module
open scoped Matrix
open cu (L)
open qAW6lac (Index block)
open qYVN5fe
private theorem a3u {K ι:Type} [za6 K] {n:ℕ}
    (M:Matrix (Fin n) (Fin n) (z3y ι K))
    (hM : ∀ i j,(M i j).totalDegree≤1) :M.det.totalDegree≤n:= by
  classical
  rw [Matrix.det_apply']
  apply zTw
  intro σ _
  have hs : (((Equiv.Perm.sign σ:ℤ) :z3y ι K)).totalDegree=0:= by
    rw [← map_intCast (znf:K →+* z3y ι K),MvPolynomial.totalDegree_C]
  have hp: (∏ j,M (σ j) j).totalDegree≤n:= by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc
      (∑ j,(M (σ j) j).totalDegree) ≤ ∑ _j:Fin n,1 :=
        Finset.sum_le_sum fun j _=>hM (σ j) j
      _=n:= by simp
  exact (zhM _ _).trans (by simpa only [hs,zero_add] using hp)
private theorem norm_relation {K A B ι:Type} [Field K] [za6 A] [Algebra K A]
    [zAa K A] [za6 B] [Fintype ι]
    (a :ι→A) (i₀:ι) (h₀:a i₀=1)
    (φ:z3y ι K →+* B) (ψ:A →+* B)
    (hC : ∀ c,φ (znf c)=ψ (algebraMap K A c))
    (hz : ∑ i,φ (z9v i)*ψ (a i)=0) :
    ∃ N :z3y ι K,N≠0∧N.totalDegree≤zsE K A∧φ N=0:= by
  classical
  let n:=zsE K A
  let b:Basis (Fin n) K A:=Module.finBasis K A
  let M:Matrix (Fin n) (Fin n) (z3y ι K) := fun r c =>
    ∑ i,z9v i*znf (b.repr (a i*b c) r)
  let ev :=zY9 (fun i:ι=>if i=i₀ then (1 :K) else 0)
  have hspec :ev.mapMatrix M=1 := by
    ext r c
    change ev (M r c)=(1 :Matrix (Fin n) (Fin n) K) r c
    simp [ev,M,ite_mul,h₀,Finsupp.single_apply,Matrix.one_apply,eq_comm]
  refine ⟨M.det,?_,a3u M ?_,?_⟩
  · intro h
    have he :ev M.det=1 := by rw [ev.map_det,hspec,Matrix.det_one]
    rw [h,map_zero] at he
    exact zero_ne_one he
  · intro r c
    apply zTw
    intro i _
    exact (zhM _ _).trans (by simp)
  let v :Fin n→B:= fun r=>ψ (b r)
  have hlin (u:A) : (∑ r,φ (znf (b.repr u r))*v r)=ψ u:= by
    simpa only [map_sum,Algebra.smul_def,map_mul,← hC,v] using
      congrArg ψ (b.sum_repr u)
  have hv :v ᵥ* φ.mapMatrix M=0:= by
    funext c
    change (∑ r,v r*φ (M r c))=0
    simp only [M,map_sum,map_mul,zxw]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i,φ (z9v i) *
          (∑ r,φ (znf (b.repr (a i*b c) r))*v r) := by
        apply zUo rfl
        intro i _
        rw [zxw]
        apply zUo rfl
        intro r _
        ac_rfl
      _=0:= by
        simp only [hlin,map_mul,← mul_assoc,← Finset.sum_mul,hz,zero_mul]
  have hkill:φ M.det•v=0:= by
    rw [φ.map_det,← Matrix.vecMul_one v,← Matrix.vecMul_smul,← Matrix.mul_adjugate,
      ← Matrix.vecMul_vecMul,hv,Matrix.zero_vecMul]
  have hentry (r :Fin n) :φ M.det*v r=0:=congrFun hkill r
  have hunit :=(hlin (1 :A)).trans (map_one ψ)
  calc
    φ M.det=φ M.det*1 :=(mul_one _).symm
    _=0:= by
      rw [← hunit,zxw]
      apply Finset.sum_eq_zero
      intro r _
      rw [mul_left_comm,hentry r,mul_zero]
private theorem local_variable {d s W:ℕ} (k :Fin 3) (i:Index d s W) :
   localizeCoeff d s W k (splitCoeff d s W k (z9v i)) =
     if h:block i=k then z9v ⟨i,h⟩
     else znf (algebraMap (FixedRing d s W k) (Ground d s W k) (z9v ⟨i,h⟩)) := by
 change (MvPolynomial.map (algebraMap (FixedRing d s W k) (Ground d s W k)))
   (MvPolynomial.sumRingEquiv L _ _ (MvPolynomial.renameEquiv L (iS d s W k)
     (z9v i)))= _
 rw [MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
 split_ifs with h
 · have he :iS d s W k i=Sum.inl ⟨i,h⟩ :=
     Equiv.sumCompl_symm_apply_of_pos (p:= fun x :Index d s W=>block x=k) h
   rw [he,MvPolynomial.sumRingEquiv_X_inl,MvPolynomial.map_X]
 · have he :iS d s W k i=Sum.inr ⟨i,h⟩ :=
     Equiv.sumCompl_symm_apply_of_neg (p:= fun x :Index d s W=>block x=k) h
   rw [he,MvPolynomial.sumRingEquiv_X_inr,MvPolynomial.map_C]
private abbrev liftPlane {K ι:Type} [za6 K] :lK K →+* lK (z3y ι K) :=
 zhd (zhd znf)
private theorem fixed_form {d s W:ℕ} (k j:Fin 3) (hj:j≠k) :
   liftPlane (pairForm d s W k j)=localForm d s W k j:= by
 rw [liftPlane,zKC,pairForm,form_map]
 unfold localForm form
 apply zUo rfl
 intro i _
 by_cases hi:block i=j
 · have hik :block i≠k := fun h=>hj (hi.symm.trans h)
   simp only [ite_eq_left hi,local_variable,dite_eq_right hik,fixedVars]
 · simp only [ite_eq_right hi]
private def phys {d s W:ℕ} {k :Fin 3} (i:Moving d s W k) :lK (Ground d s W k) :=
 zdM (yDeg i.val) (zdM (xDeg i.val) 1)
private theorem moving_form {d s W:ℕ} (k :Fin 3) :
    localForm d s W k k = ∑ i:Moving d s W k,
      z1z (z1z (z9v i)) *
        liftPlane (phys i) := by
  rw [localForm,form,← Finset.sum_filter,← Finset.sum_subtype_eq_sum_filter,Finset.subtype_univ]
  apply zUo rfl
  intro i _
  simp only [local_variable,dite_eq_left i.prop,phys,liftPlane,Polynomial.map_monomial,
    zKC,map_one,Polynomial.C_mul_monomial,mul_one]
private theorem constant_slot (d s W:ℕ) (k :Fin 3) :
   ∃ i:Moving d s W k,phys i=1 := by
 suffices h : ∃ i:Moving d s W k,yDeg i.val=0∧xDeg i.val=0 by
   obtain ⟨i,hy,hx⟩:=h
   exact ⟨i,by simp only [phys,hy,hx,Polynomial.monomial_zero_one]⟩
 fin_cases k
 · exact ⟨⟨.inl ⟨(0,0),by simp⟩,rfl⟩,rfl,rfl⟩
 · exact ⟨⟨.inr (.inl ⟨(0,0),by simp⟩),rfl⟩,rfl,rfl⟩
 · exact ⟨⟨.inr (.inr ⟨(0,0),by simp⟩),rfl⟩,rfl,rfl⟩
private theorem plane_norm {K ι:Type} [Field K] [Fintype ι]
   (F G:lK K) (a :ι→lK K) [zAa K (pairQuot F G)]
   (i₀:ι) (h₀:a i₀=1) (I:Ideal (lK (z3y ι K)))
   (hF:liftPlane F∈I) (hG:liftPlane G∈I)
   (ha : (∑ i,z1z (z1z (z9v i))*liftPlane (a i))∈I) :
   ∃ N :z3y ι K,N≠0∧N.totalDegree≤zsE K (pairQuot F G) ∧
     z1z (z1z N)∈I:= by
 let J:Ideal (lK K) :=zye ({F,G} : Set (lK K))
 let A:=pairQuot F G
 let:za6 A:=Ideal.Quotient.commRing J
 let:Algebra K A:=Ideal.Quotient.algebra K (I:=J)
 let R:=z3y ι K
 let:za6 R:=AddMonoidAlgebra.commRing
 let P:=zM1 (zM1 R)
 let:za6 P := @zqU (zM1 R) (zqU (R:=R))
 let B:=P ⧸ I
 let q:P →+* B:=zVv I
 have hJ : ∀ f∈J,(q.comp liftPlane) f=0:= by
   suffices J≤RingHom.ker (q.comp liftPlane) from fun _ hf=>this hf
   apply Ideal.span_le.mpr
   intro f hf
   change q (liftPlane f)=0
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
   rcases hf with rfl | rfl
   · exact Ideal.Quotient.eq_zero_iff_mem.mpr hF
   · exact Ideal.Quotient.eq_zero_iff_mem.mpr hG
 let ψ:A →+* B:=Ideal.Quotient.lift J (q.comp liftPlane) hJ
 let φ:z3y ι K →+* B:=q.comp (Polynomial.C.comp z1z)
 let mkJ:lK K →+* A:=zVv J
 have hψ (f :lK K) :ψ (mkJ f)=q (liftPlane f) :=rfl
 have hC (c:K) :φ (znf c)=ψ (algebraMap K A c) := by
   change q (z1z (z1z (znf c))) =
     ψ (mkJ (z1z (z1z c)))
   simp only [hψ,liftPlane,zKC,Polynomial.map_C]
   rfl
 have hz : ∑ i,φ (z9v i)*ψ (mkJ (a i))=0:= by
   change (∑ i,q (z1z (z1z (z9v i)))*ψ (mkJ (a i)))=0
   simp only [hψ,← map_mul q,← map_sum q]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
 have h₁:mkJ (a i₀)=1 := by rw [h₀,map_one]
 obtain ⟨N,hN,hd,hvan⟩:=norm_relation (fun i=>mkJ (a i)) i₀ h₁ φ ψ hC hz
 exact ⟨N,hN,hd,Ideal.Quotient.eq_zero_iff_mem.mp hvan⟩
theorem proof :qYVN5fe.c3:= by
 intro d s W _ _ _ _ _ k hfinite
 let:zAa (Ground d s W k) (PairAlgebra d s W k) :=hfinite
 obtain ⟨i₀,hi⟩:=constant_slot d s W k
 let I:Ideal (lK (LocalRing d s W k)) :=zye (Set.range (localForm d s W k))
 have hmem (j:Fin 3) :localForm d s W k j∈I:=Ideal.subset_span (Set.mem_range_self j)
 have hfixed (j:Fin 3) (hj:j≠k) :liftPlane (pairForm d s W k j)∈I:= by
  rw [fixed_form k j hj]
  exact hmem j
 refine plane_norm (pairForm d s W k (left k)) (pairForm d s W k (right k)) phys i₀ hi I
  (hfixed _ (by fin_cases k <;> decide)) (hfixed _ (by fin_cases k <;> decide)) ?_
 rw [← moving_form]
 exact hmem k
end
end qrtGZca
end
end
