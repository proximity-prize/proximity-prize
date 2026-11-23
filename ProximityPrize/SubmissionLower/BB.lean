import ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.Polynomial.UniqueFactorization
set_option Elab.async false
open _root_ renaming AddCommGroup→sH,Algebra→ oK,Algebra.algebraMap→aU,Cardinal→ oy,Cardinal.natCast_add_one_le_iff→yo,CommRing→cy,DFunLike.congr_fun→qJ,ENat.toNat→p9,ENat.toNat_add→qm,Equiv.optionSubtypeNe→qz,Equiv.optionSubtypeNe_symm_of_ne→yl,Finset→qx,Finset.prod_insert→zg,Finset.sum_congr→pQ,Finset.sum_filter→yB,Finset.sum_le_sum→yQ,Finsupp.degree_apply→zh,Function.Exact→p6,Function.Injective→qM,Function.Surjective→p7,Ideal→lV,Ideal.Quotient.mk→n5,Ideal.Quotient.mk_surjective→qG,Ideal.comap_map_of_surjective→x7,Ideal.map_span→pC,Ideal.mem_map_of_mem→t4,Ideal.mem_span_singleton→zm,Ideal.mk_ker→uh,Ideal.pow_le_self→y5,Ideal.span→lz,Ideal.span_singleton_le_iff_mem→zk,Ideal.subset_span→xW,IsLocalRing.maximalIdeal→uW,IsLocalization→qy,IsLocalization.algebraMap_mem_map_algebraMap_iff→vZ,IsLocalization.map_units→t3,IsNoetherianRing→t6,IsUnit→ oZ,LinearIndependent→qU,LinearMap.exact_iff→xu,LinearMap.exact_map_mkQ_range→u5,LinearMap.exact_subtype_ker_map→t9,LinearMap.range→lJ,Localization.AtPrime→ oD,Localization.Away→zc,Module→nX,Module.Finite→t5,Module.compHom→ ox
open _root_ renaming Module.finrank→u9,Module.length→lI,Module.length_eq_add_of_exact→wB,Module.length_eq_zero→ze,Module.length_quotient→yU,Module.rank→ ov,MvPolynomial→c9,MvPolynomial.C→pG,MvPolynomial.X→sI,MvPolynomial.constantCoeff→vh,MvPolynomial.eval→vH,MvPolynomial.homogeneousComponent→vj,MvPolynomial.homogeneousComponent_apply→zd,MvPolynomial.le_totalDegree→th,MvPolynomial.map→ oj,MvPolynomial.map_C→xm,MvPolynomial.map_X→xL,MvPolynomial.optionEquivLeft→uJ,MvPolynomial.renameEquiv_apply→xI,Nat.not_succ_le_self→zf,Nontrivial→vi,Order.coheight_eq_krullDim_Ici→zi,Polynomial→vk,Polynomial.C→nq,Polynomial.X→pL,Polynomial.coeff_C_mul→wY,Polynomial.coeff_zero→vl,Polynomial.evalRingHom→wA,Polynomial.mapRingHom→v9,Polynomial.map_mul→yJ,RingHom.comp_apply→yL,RingHom.ker→pz,RingHom.mem_ker→u8,Set.image_singleton→p5,Submodule→uz,Submodule.mkQ_surjective→vG,Submodule.subtype_injective→v8,Submonoid.powers→sS,Subtype.ext→wR,congrArg→nI,le_sup_left→vw,lt_of_le_of_ne→t8,map_mul→mD,map_pow→pU,map_smul→t7,map_sum→ oz,map_zero→ oq,mul_assoc→ oY
set_option autoImplicit true
section
namespace axd
noncomputable section
open scoped BigOperators Polynomial
set_option linter.style.haveILetI false
section
variable {R A B:Type} [cy R] [cy A] [IsDomain A] [cy B]
variable (ρ:R[X] →+* A) (τ:R →+* B) (s :A →+* B)
private theorem en6 (hw:ρ pL≠0)
    (hs :s.comp ρ=τ.comp (wA 0)) {n:ℕ} (v :Fin n→A) :
    letI:nX R[X] A:=ox A ρ
    letI:nX R B:=ox B τ
    qU R (s ∘ v)→qU R[X] v := by
  classical
  letI:nX R[X] A:=ox A ρ
  letI:nX R B:=ox B τ
  change qU R (s ∘ v)→qU R[X] v
  intro hv
  have specialize (f :Fin n→R[X]) (hf : ∑ i,ρ (f i)*v i=0) :
      ∀ i,(f i).coeff 0=0:= by
    have hcompat (p:R[X]) :s (ρ p)=τ (p.coeff 0) := by
      simpa only [yL,Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coe_evalRingHom] using
        qJ hs p
    have h:=nI s hf
    rw [oz ,oq] at h
    simp only [mD,hcompat] at h
    exact Fintype.linearIndependent_iff.mp hv (fun i=>(f i).coeff 0) h
  have allCoeffs (k :ℕ) (f :Fin n→R[X]) (hf : ∑ i,ρ (f i)*v i=0) :
      ∀ i,(f i).coeff k=0:= by
    induction k generalizing f with
    | zero=>exact specialize f hf
    | succ k ih =>
      have hdiv (i:Fin n) :pL*(f i).divX=f i:= by
        simpa [specialize f hf i] using Polynomial.X_mul_divX_add (f i)
      have hprod:ρ pL * ∑ i,ρ ((f i).divX)*v i=0:= by
        rw [Finset.mul_sum]
        simp_rw [← oY ,← mD,hdiv]
        exact hf
      have hrel :=(mul_eq_zero.mp hprod).resolve_left hw
      intro i
      simpa only [Polynomial.coeff_divX] using ih (fun i=>(f i).divX) hrel i
  refine Fintype.linearIndependent_iff.mpr fun f hf i => ?_
  ext k
  rw [vl]
  exact allCoeffs k f hf i
theorem fTi [vi R] (hw:ρ pL≠0)
  (hs :s.comp ρ=τ.comp (wA 0))
  (hsurj:p7 s) (n:ℕ) :
  letI:nX R[X] A:=ox A ρ
  letI:nX R B:=ox B τ
  ov R[X] A≤(n:oy)→ ov R B≤(n:oy) := by
 classical
 letI:nX R[X] A:=ox A ρ
 letI:nX R B:=ox B τ
 change ov R[X] A≤(n:oy)→ ov R B≤(n:oy)
 intro hrank
 by_contra! h
 have hlarge : ((n+1 :ℕ) :oy)≤ov R B:= by
  rwa [Nat.cast_add_one,yo]
 obtain ⟨v,hv⟩:=Module.le_rank_iff.mp hlarge
 choose u hu using fun i=>hsurj (v i)
 have hu' : s ∘ u=v :=funext hu
 have hind:=en6 ρ τ s hw hs u (hu' ▸ hv)
 have hsmall: ((n+1 :ℕ) :oy)≤ov R[X] A :=
  Module.le_rank_iff.mpr ⟨u,hind⟩
 exact (zf n) (by exact_mod_cast hsmall.trans hrank)
end
theorem fTh {R A B:Type} [cy R] [IsDomain R]
   [cy A] [cy B] [IsDomain B] (ρ:R →+* A) (τ:R →+* B) (s :A →+* B)
   (hs :s.comp ρ=τ) (b:A) (hb:s b≠0)
   (hrec : ∀ a :B,∃ q:A,∃ m:ℕ,s q=s b^m*a) (n:ℕ) :
   letI:nX R A:=ox A ρ
   letI:nX R B:=ox B τ
   ov R A≤(n:oy)→ ov R B≤(n:oy) := by
 classical
 letI:nX R A:=ox A ρ
 letI:nX R B:=ox B τ
 change ov R A≤(n:oy)→ ov R B≤(n:oy)
 intro hrank
 by_contra! h
 have hlarge : ((n+1 :ℕ) :oy)≤ov R B:= by
   rwa [Nat.cast_add_one,yo]
 obtain ⟨v,hv⟩:=Module.le_rank_iff.mp hlarge
 choose q m hm using fun i=>hrec (v i)
 let k :=Finset.univ.sup m
 let u (i:Fin (n+1)) :=b^(k - m i)*q i
 have hu (i:Fin (n+1)) :s (u i)=s b^k*v i:= by
   have hi:m i≤k :=Finset.le_sup (Finset.mem_univ i)
   change s (b^(k - m i)*q i)=s b^k*v i
   rw [mD,pU,hm,← oY ,← pow_add,Nat.sub_add_cancel hi]
 have hind:qU R u:= by
   refine Fintype.linearIndependent_iff.mpr fun f hf => ?_
   have hf' : ∑ i,ρ (f i)*u i=0:=hf
   have h:=nI s hf'
   have hcomp (r :R) :s (ρ r)=τ r :=qJ hs r
   rw [oz ,oq] at h
   simp only [mD,hu,hcomp] at h
   have hprod:s b^k * ∑ i,τ (f i)*v i=0:= by
     simpa only [Finset.mul_sum,mul_left_comm] using h
   exact Fintype.linearIndependent_iff.mp hv f
     ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ hb))
 have hsmall: ((n+1 :ℕ) :oy)≤ov R A :=
   Module.le_rank_iff.mpr ⟨u,hind⟩
 exact (zf n) (by exact_mod_cast hsmall.trans hrank)
end
end axd
end
section
namespace bzw
noncomputable section
open scoped BigOperators Polynomial
variable {F R S σ:Type} [Field F] [cy R] [cy S]
def aDn (f :F →+* R) (g:c9 σ F) (x :σ→R) (w:R) :R :=
  ∑ d∈g.support,f (g.coeff d)*(∏ i∈d.support,x i^d i) *
    w^(g.totalDegree - d.degree)
theorem b8D (k :R →+* S) (f :F →+* R) (g:c9 σ F)
  (x :σ→R) (w:R) :
  k (aDn f g x w)=aDn (k.comp f) g (k ∘ x) (k w) := by
 simp [aDn,oz ,map_prod]
theorem enj (f :F →+* R) (g:c9 σ F) (x :σ→R) :
   aDn f g x 0=(vj g.totalDegree g).eval₂ f x := by
 classical
 rw [zd ,MvPolynomial.eval₂_sum,yB]
 apply pQ rfl
 intro d hd
 have hle :d.degree≤g.totalDegree :=th hd
 by_cases he :d.degree=g.totalDegree
 · simp [he,MvPolynomial.eval₂_monomial,Finsupp.prod]
 · simp [he,zero_pow (Nat.sub_ne_zero_of_lt (t8 hle he))]
theorem enh (f :F →+* R) (g:c9 σ F) (x :σ→R) (w:R) :
  aDn f g (fun i=>x i*w) w=g.eval₂ f x*w^g.totalDegree := by
 rw [aDn,MvPolynomial.eval₂_eq,Finset.sum_mul]
 apply pQ rfl
 intro d hd
 have hle :d.degree≤g.totalDegree :=th hd
 simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
 rw [← zh]
 rw [← oY (f _),oY (f _ * ∏ i∈d.support,x i^d i),
  ← pow_add,Nat.add_sub_of_le hle]
open Polynomial in
private theorem dMv {ι:Type} (s :qx ι) (p:ι→R[X]) (n:ι→ℕ)
    (h : ∀ i∈s,(p i).natDegree≤n i) :
    (∏ i∈s,p i).coeff (∑ i∈s,n i) = ∏ i∈s,(p i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | insert i s hi ih =>
    have hs : ∀ j∈s,(p j).natDegree≤n j:= fun j hj=>h j (Finset.mem_insert_of_mem hj)
    rw [zg hi,Finset.sum_insert hi,zg hi,
      coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self i s))
        ((natDegree_prod_le s p).trans (yQ hs)),ih hs]
def a5s (f :F →+* R) (g:c9 σ F)
    (v :σ→F) (a :σ→R) (w:R) :R[X] :=
  aDn (Polynomial.C.comp f) g
    (fun i=>nq (a i)+Polynomial.C (f (v i))*pL) (nq w)
open Polynomial in
theorem ewD (f :F →+* R) (g:c9 σ F)
    (v :σ→F) (a :σ→R) (w:R) :
    (a5s f g v a w).natDegree≤g.totalDegree ∧
    (a5s f g v a w).coeff g.totalDegree =
      f (vH v (vj g.totalDegree g)) := by
  classical
  let q:σ→R[X] := fun i=>C (a i)+C (f (v i))*X
  have hq (i:σ) : (q i).natDegree≤1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · simpa only [pow_one] using natDegree_C_mul_X_pow_le (f (v i)) 1
  have hqcoeff (i:σ) : (q i).coeff 1=f (v i) := by
    simp [q,coeff_add]
  let term (d:σ →₀ ℕ) :R[X] :=
    C (f (g.coeff d)*w^(g.totalDegree - d.degree)) * ∏ i∈d.support,q i^d i
  have hterm (d:σ →₀ ℕ) : (term d).natDegree≤d.degree := by
    apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_prod_le _ _).trans (yQ fun i _=> by
      simpa using natDegree_pow_le_of_le (d i) (hq i))
  have hsum:a5s f g v a w = ∑ d∈g.support,term d:= by
    unfold a5s aDn
    apply pQ rfl
    intro d _
    simp only [term,yL,mD,pU]
    ring
  rw [hsum]
  refine ⟨natDegree_sum_le_of_forall_le _ _ (fun d hd=>(hterm d).trans
    (th hd)),?_⟩
  rw [finsetSum_coeff,zd ,oz ,oz ,
    yB]
  apply pQ rfl
  intro d hd
  have hle :d.degree≤g.totalDegree :=th hd
  by_cases he :d.degree=g.totalDegree
  · have hprod :
        (∏ i∈d.support,q i^d i).coeff d.degree =
          ∏ i∈d.support,f (v i^d i) := by
      rw [zh,dMv d.support (fun i=>q i^d i) d
        (fun i _=> by simpa using natDegree_pow_le_of_le (d i) (hq i))]
      apply Finset.prod_congr rfl
      intro i _
      simpa [hqcoeff,Nat.mul_one] using
        (coeff_pow_of_natDegree_le (m:=d i) (hq i))
    simp only [he,↓reduceIte,Nat.sub_self,pow_zero,mul_one,term,wY]
    rw [← he,hprod]
    simp [MvPolynomial.eval_monomial,Finsupp.prod,mD,map_prod]
  · simp [he,coeff_eq_zero_of_natDegree_lt ((hterm d).trans_lt (t8 hle he))]
def aIE (f :F →+* R) (g:c9 σ F)
    (v :σ→F) (a :σ→R) (w:R) :R[X] :=
  nq (f (vH v (vj g.totalDegree g))⁻¹) *
    a5s f g v a w
open Polynomial in
theorem c0J [vi R] (f :F →+* R) (g:c9 σ F)
  (v :σ→F) (a :σ→R) (w:R)
  (hv :vH v (vj g.totalDegree g)≠0) :
  (aIE f g v a w).Monic∧(aIE f g v a w).natDegree=g.totalDegree := by
 obtain ⟨hd,hc⟩:=ewD f g v a w
 have hcoeff : (aIE f g v a w).coeff g.totalDegree=1 := by
  rw [aIE,wY ,hc,← mD,inv_mul_cancel₀ hv,map_one]
 have hdeg: (aIE f g v a w).natDegree=g.totalDegree :=
  natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_C_mul_le _ _).trans hd)
    (by rw [hcoeff]; exact one_ne_zero)
 exact ⟨by rwa [Monic,leadingCoeff,hdeg],hdeg⟩
open Polynomial in
theorem c0I (f :F →+* R) (g:c9 σ F) (v :σ→F)
  (a :σ→R) (w:R) (ρ:R →+* S) (z :S)
  (h:aDn (ρ.comp f) g (fun i=>ρ (a i)+ρ (f (v i))*z) (ρ w)=0) :
  (aIE f g v a w).eval₂ ρ z=0:= by
 have hf : (eval₂RingHom ρ z).comp (C.comp f)=ρ.comp f := by
  ext r
  simp [eval₂_C]
 have hline : (eval₂RingHom ρ z) (a5s f g v a w)=0:= by
  rw [a5s,b8D,hf]
  simpa [Function.comp_def,map_add,mD,coe_eval₂RingHom,eval₂_C,eval₂_X] using h
 change (eval₂RingHom ρ z) (aIE f g v a w)=0
 rw [aIE,mD,hline,mul_zero]
end
end bzw
end
section
set_option maxHeartbeats 800000
namespace bzy
noncomputable section
open MvPolynomial
theorem d0U {A τ:Type*} [cy A] [vi A]
    (s :qx τ) (c:τ) (hc:c∈s) (v :τ→A) (hv :v c=1) :
    let g:c9 τ A := ∑ m∈s,sI m*pG (v m)
    g≠0 ∧
      ∃ f :c9 τ A →+* c9 {m // m≠c} A,
        pz f=lz {g} ∧ f.comp pG=MvPolynomial.C:= by
  classical
  let B:=c9 {m // m≠c} A
  let e :c9 τ A ≃ₐ[A] vk B :=
    (renameEquiv A (qz c).symm).trans (uJ A _)
  let g:c9 τ A := ∑ m∈s,sI m*pG (v m)
  let y :B := ∑ m∈s.erase c,if hm:m≠c then sI ⟨m,hm⟩*pG (v m) else 0
  have eC (a :A) :e (pG a)=nq (pG a) := by
    change uJ A _ (rename (qz c).symm (pG a))= _
    rw [rename_C,optionEquivLeft_C]
  have eX (m:τ) :e (sI m)=match (qz c).symm m with
      | none=>Polynomial.X
      | some n=>Polynomial.C (MvPolynomial.X n) := by
    change uJ A _ (rename (qz c).symm (sI m))= _
    rw [rename_X]
    cases (qz c).symm m with
    | none=>exact optionEquivLeft_X_none A _
    | some n=>exact optionEquivLeft_X_some A _ n
  have eg:e g=pL+Polynomial.C y := by
    dsimp only [g,y]
    rw [← Finset.sum_erase_add _ _ hc,map_add,oz ,oz ,add_comm]
    congr 1
    · rw [hv,map_one,mul_one,eX,Equiv.optionSubtypeNe_symm_self]
    · apply pQ rfl
      intro m hm
      have hmc:=Finset.ne_of_mem_erase hm
      rw [dite_eq_left hmc,mD,eX,yl hmc,eC,mD]
  change g≠0∧_
  refine ⟨?_,(wA (-y)).comp e.toRingHom,?_,?_⟩
  · intro hg
    have h:=nI (fun p:vk B=>p.coeff 1) (eg.symm.trans (hg ▸ e.map_zero))
    simp at h
  · rw [← RingHom.comap_ker,Polynomial.ker_evalRingHom]
    have hh:pL-Polynomial.C (-y)=e.toRingHom g:= by
      change pL-Polynomial.C (-y)=e g
      rw [eg,map_neg,sub_neg_eq_add]
    rw [hh,← p5 (f :=e.toRingHom) (a :=g),← pC]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  · apply RingHom.ext
    intro a
    change Polynomial.eval (-y) (e (pG a))=pG a
    rw [eC,Polynomial.eval_C]
end
end bzy
end
section
namespace aA2
noncomputable section
private theorem dPA {R S:Type*}
    [cy R] [t6 R] [IsLocalRing R] [cy S] [oK R S]
    (M:Submonoid R) [qy M S] {a :R}
    (ha :a∈uW R) (hu:oZ (aU R S a)) :
    StrictMono (fun J:lV S=>J.under R ⊔ lz {a}) := by
  intro J K hJK
  have hle :=(IsLocalization.orderEmbedding M S).monotone hJK.le
  refine t8 (sup_le_sup_right hle _) ?_
  intro heq
  change J.under R ⊔ lz {a} = K.under R ⊔ lz {a} at heq
  have hcontain:K.under R≤J.under R ⊔ lz {a} * K.under R:= by
    intro b hb
    have hb' : b∈J.under R ⊔ lz {a} := by
      rw [heq]
      exact Ideal.mem_sup_left hb
    obtain ⟨j,hj,c,hc,rfl⟩:=Submodule.mem_sup.mp hb'
    obtain ⟨d,rfl⟩:=Ideal.mem_span_singleton.mp hc
    have had:a*d∈K.under R:= by
      rw [← add_sub_cancel_left j (a*d)]
      exact (K.under R).sub_mem hb (hle hj)
    have hd:d∈K.under R:= by
      change aU R S d∈K
      have hh:aU R S a*aU R S d∈K:= by
        rw [← mD]
        exact had
      obtain ⟨u,hu⟩:=hu
      rw [← hu] at hh
      simpa [← oY] using K.mul_mem_left (↑u⁻¹:S) hh
    exact Submodule.mem_sup.mpr ⟨j,hj,a*d,
      Ideal.mem_span_singleton_mul.mpr ⟨d,hd,rfl⟩,rfl⟩
  have hback :K.under R≤J.under R :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      ((zk _).mpr
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : lV R) ha)) hcontain
  exact hJK.not_ge ((IsLocalization.under_le_under_iff M S).mp hback)
private theorem evO {R S:Type*}
  [cy R] [t6 R] [IsLocalRing R] [cy S] [oK R S]
  (M:Submonoid R) [qy M S] (I:lV R) {a :R}
  (ha :a∈uW R) (hu:oZ (aU R S a)) :
  lI S (S ⧸ I.map (aU R S))≤lI R (R ⧸ (I ⊔ lz {a})) := by
 let F:Set.Ici (I.map (aU R S))→Set.Ici (I ⊔ lz {a}) := fun J =>
  ⟨J.1.under R ⊔ lz {a},sup_le_sup_right (Ideal.map_le_iff_le_comap.mp J.2) _⟩
 have hF:StrictMono F:= fun _ _ h=>dPA M ha hu h
 rw [← WithBot.coe_le_coe,yU,yU,
  zi ,zi]
 exact Order.krullDim_le_of_strictMono F hF
theorem cXp {R:Type*}
   [cy R] [t6 R] {P Q I:lV R} [P.IsPrime] [Q.IsPrime]
   (hPQ:P≤Q) {a :R} (haQ:a∈Q) (haP:a∉P) :
   let A:=oD P
   let B:=oD Q
   lI A (A ⧸ I.map (aU R A)) ≤
     lI B (B ⧸ (I ⊔ lz {a}).map (aU R B)) := by
 let A:=oD P
 let B:=oD Q
 have hsub:Q.primeCompl≤P.primeCompl:= fun _ h=> fun hp=>h (hPQ hp)
 change lI A (A ⧸ I.map (aU R A)) ≤
   lI B (B ⧸ (I ⊔ lz {a}).map (aU R B))
 let:oK B A:=IsLocalization.localizationAlgebraOfSubmonoidLe B A _ _ hsub
 let:IsScalarTower R B A:=IsLocalization.localization_isScalarTower_of_submonoid_le B A _ _ hsub
 let:qy (P.primeCompl.map (aU R B)) A :=
   IsLocalization.isLocalization_of_submonoid_le B A _ _ hsub
 have ha :aU R B a∈uW B:= by
   change a∈(uW B).under R
   rwa [IsLocalization.AtPrime.under_maximalIdeal B Q]
 have hu:oZ (aU B A (aU R B a)) := by
   rw [← IsScalarTower.algebraMap_apply]
   exact t3 A (⟨a,haP⟩:P.primeCompl)
 have he :=evO (P.primeCompl.map (aU R B))
   (I.map (aU R B)) ha hu
 rw [Ideal.map_map,← IsScalarTower.algebraMap_eq R B A] at he
 rwa [Ideal.map_sup,pC,p5]
end
end aA2
end
section
namespace aRX
open LinearMap
section Euler
variable {R:Type*} [cy R]
variable {M N P:Type*} [sH M] [sH N] [sH P]
variable [nX R M] [nX R N] [nX R P]
def aAR (t:R) (M:Type*) [sH M] [nX R M] :Prop :=
  lI R (ker (lsmul R M t)) < ⊤ ∧
    lI R (M ⧸ lJ (lsmul R M t)) < ⊤
noncomputable def auJ (t:R) (M:Type*) [sH M] [nX R M] :ℤ :=
 ((lI R (M ⧸ lJ (lsmul R M t))).toNat :ℤ) -
   (lI R (ker (lsmul R M t))).toNat
theorem brL (v :M →ₗ[R] N) :
  lI R M=lI R (ker v)+Module.length R (lJ v) := by
 refine wB (ker v).subtype v.rangeRestrict
  (v8 _) v.surjective_rangeRestrict ?_
 rw [xu,Submodule.range_subtype,LinearMap.ker_rangeRestrict]
theorem evR (v :M →ₗ[R] N) :
  lI R N=lI R (lJ v)+Module.length R (N ⧸ lJ v) :=
 wB (lJ v).subtype (lJ v).mkQ
  (v8 _) (vG _)
  (LinearMap.exact_subtype_mkQ _)
theorem dSA (t:R) (f :M →ₗ[R] N) (g:N →ₗ[R] P)
    (hf :qM f) (hg:p7 g) (hfg:p6 f g)
    (hM:aAR t M) (hP:aAR t P) :
    aAR t N∧auJ t N=auJ t M+auJ t P:= by
  let a :=lsmul R M t
  let b:=lsmul R N t
  let c:=lsmul R P t
  have hab:g.comp b=c.comp g:= by ext x; simp [b,c]
  have hbc:f.comp a=b.comp f := by ext x; simp [a,b]
  let fK:ker a →ₗ[R] ker b:=(f.comp (ker a).subtype).codRestrict _ (by
    intro x
    change t•f x.val=0
    rw [← t7]
    exact (nI f x.property).trans (oq f))
  let gK:ker b →ₗ[R] ker c:=(g.comp (ker b).subtype).codRestrict _ (by
    intro x
    change t•g x.val=0
    rw [← t7]
    exact (nI g x.property).trans (oq g))
  let fC:=Submodule.mapQ (lJ a) (lJ b) f (by
    rintro _ ⟨x,rfl⟩
    exact ⟨f x,(qJ hbc x).symm⟩)
  let gC:=Submodule.mapQ (lJ b) (lJ c) g (by
    rintro _ ⟨x,rfl⟩
    exact ⟨g x,(qJ hab x).symm⟩)
  let δ:=SnakeLemma.δ' a b c f g hfg f g hfg hbc hab
    (ker c).subtype (t9 c) (lJ a).mkQ
    (u5 a) hg hf
  have hfK:qM fK:= fun x y h=>wR (hf (nI Subtype.val h))
  have hgC:p7 gC:= by
    intro x
    obtain ⟨x,rfl⟩:=vG _ x
    obtain ⟨y,rfl⟩:=hg x
    exact ⟨(lJ b).mkQ y,rfl⟩
  have hk :p6 fK gK:= by
    intro x
    constructor
    · intro hx
      obtain ⟨y,hy⟩:=(hfg x.val).mp (nI Subtype.val hx)
      have hay :a y=0:=hf (by
        simpa [hy,x.property] using qJ hbc y)
      exact ⟨⟨y,hay⟩,wR hy⟩
    · rintro ⟨y,rfl⟩
      exact wR (hfg.apply_apply_eq_zero y.val)
  have hkδ:p6 gK δ :=
    SnakeLemma.exact_δ'_right a b c f g hfg f g hfg hbc hab
      (ker b).subtype (t9 b)
      (ker c).subtype (t9 c)
      (lJ a).mkQ (u5 a) hg hf gK rfl
      (v8 _)
  have hδc:p6 δ fC :=
    SnakeLemma.exact_δ'_left a b c f g hfg f g hfg hbc hab
      (ker c).subtype (t9 c)
      (lJ a).mkQ (u5 a)
      (lJ b).mkQ (u5 b) hg hf fC rfl
      (vG _)
  have hc:p6 fC gC:= by
    apply (hfg.exact_mapQ_iff _ _).2
    rw [show lJ g = ⊤ from LinearMap.range_eq_top.mpr hg,top_inf_eq]
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,rfl⟩:=hg x
    exact ⟨b y,⟨y,rfl⟩,qJ hab y⟩
  change lI R (ker a) < ⊤ ∧ lI R (M ⧸ lJ a) < ⊤ at hM
  change lI R (ker c) < ⊤ ∧ lI R (P ⧸ lJ c) < ⊤ at hP
  have l1 :=brL gK
  rw [hk.linearMap_ker_eq,← (LinearEquiv.ofInjective fK hfK).length_eq] at l1
  have l2 :=brL δ
  rw [hkδ.linearMap_ker_eq] at l2
  have l3:=brL fC
  rw [hδc.linearMap_ker_eq] at l3
  have l4 :=brL gC
  rw [hc.linearMap_ker_eq,LinearMap.range_eq_top.mpr hgC,Module.length_top] at l4
  have h2 :=ENat.add_lt_top.mp (l2 ▸ hP.1)
  have h3:=ENat.add_lt_top.mp (l3 ▸ hM.2)
  refine ⟨⟨l1.symm ▸ ENat.add_lt_top.mpr ⟨hM.1,h2.1⟩,
      l4.symm ▸ ENat.add_lt_top.mpr ⟨h3.2,hP.2⟩⟩,?_⟩
  have n1 :=nI p9 l1
  have n2 :=nI p9 l2
  have n3:=nI p9 l3
  have n4 :=nI p9 l4
  rw [qm hM.1.ne h2.1.ne] at n1
  rw [qm h2.1.ne h2.2.ne] at n2
  rw [qm h3.1.ne h3.2.ne] at n3
  rw [qm h3.2.ne hP.2.ne] at n4
  unfold auJ
  change ((lI R (N ⧸ lJ b)).toNat :ℤ)-(lI R (ker b)).toNat =
    ((lI R (M ⧸ lJ a)).toNat :ℤ)-(lI R (ker a)).toNat +
      (((lI R (P ⧸ lJ c)).toNat :ℤ)-(lI R (ker c)).toNat)
  omega
theorem cI0 (t:R) (e :M ≃ₗ[R] N) :
   (aAR t M↔aAR t N)∧auJ t M=auJ t N := by
 let a :=lsmul R M t
 let b:=lsmul R N t
 have hker : (ker a).map e.toLinearMap=ker b:= by
   ext y
   obtain ⟨x,rfl⟩:=e.surjective y
   constructor
   · rintro ⟨z,hz,ezy⟩
     have hx :a x=0:=e.injective ezy ▸ hz
     show t•e x=0
     rw [← t7,show t•x=0 from hx,oq]
   · intro hx
     exact ⟨x,e.injective (by simpa [a,b] using hx),rfl⟩
 have hrange : (lJ a).map e.toLinearMap=lJ b:= by
   ext y
   constructor
   · rintro ⟨_,⟨x,rfl⟩,rfl⟩
     exact ⟨e x,by simp [a,b]⟩
   · rintro ⟨x,rfl⟩
     obtain ⟨z,rfl⟩:=e.surjective x
     exact ⟨a z,⟨z,rfl⟩,by simp [a,b]⟩
 have lk :=(e.ofSubmodules (ker a) (ker b) hker).length_eq
 have lc:=(Submodule.Quotient.equiv (lJ a) (lJ b) e hrange).length_eq
 unfold aAR auJ
 rw [lk,lc]
 exact ⟨Iff.rfl,rfl⟩
theorem cI7 (t:R) (h:lI R M < ⊤) :
  aAR t M∧auJ t M=0:= by
 let a :=lsmul R M t
 have lk :=brL a
 have lc:=evR a
 have hk :=ENat.add_lt_top.mp (lk ▸ h)
 have hc:=ENat.add_lt_top.mp (lc ▸ h)
 refine ⟨⟨hk.1,hc.2⟩,?_⟩
 have h₁:=nI p9 lk
 have h₂:=nI p9 lc
 rw [qm hk.1.ne hk.2.ne] at h₁
 rw [qm hc.1.ne hc.2.ne] at h₂
 unfold auJ
 change ((lI R (M ⧸ lJ a)).toNat :ℤ)-(lI R (ker a)).toNat=0
 omega
end Euler
end aRX
end
section
namespace aRV
noncomputable section
open MvPolynomial
abbrev Vars (K:Type*) [cy K] (n:ℕ) :=idealOfVars (Fin n) K
abbrev gQ (K:Type*) [cy K] (n t:ℕ) :=
 c9 (Fin n) K ⧸ Vars K n^t
abbrev jet (K:Type*) [cy K] (n t:ℕ) :
 c9 (Fin n) K →+* gQ K n t:=n5 _
abbrev aug (K:Type*) [cy K] (n t:ℕ) :lV (gQ K n t) :=
 (Vars K n).map (jet K n t)
theorem bbP (K:Type*) [cy K] (n t:ℕ) :
  aug K n t^t = ⊥ := by
 rw [← Ideal.map_pow,Ideal.map_eq_bot_iff_le_ker,uh]
theorem duX (K:Type*) [cy K] (n t:ℕ) :
  aug K n t=lz (Set.range fun i=>jet K n t (X i)) := by
 change (lz (Set.range X)).map (jet K n t)= _
 rw [pC,← Set.range_comp]
 rfl
theorem dqI (K:Type*) [cy K] (n t:ℕ) (i:Fin n) :
  jet K n t (X i)∈aug K n t :=
 t4 _ (xW ⟨i,rfl⟩)
theorem ker_constantCoeff (K:Type*) [cy K] (n:ℕ) :
   pz (vh :c9 (Fin n) K →+* K)=Vars K n:= by
 ext p
 rw [u8 ,← pow_one (Vars K n),mem_pow_idealOfVars_iff']
 change p.coeff 0=0↔_
 constructor
 · intro h d hd
   obtain rfl :d=0:=(Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
   exact h
 · intro h
   exact h 0 (by simp)
abbrev constant (K:Type*) [cy K] (n t:ℕ) (ht:0<t) :
  gQ K n t →+* K :=
 Ideal.Quotient.lift _ vh <| by
  change Vars K n^t≤pz (vh :c9 (Fin n) K →+* K)
  rw [ker_constantCoeff]
  exact y5 ht.ne'
@[simp] theorem dO7 (K:Type*) [cy K] (n t:ℕ) (ht:0<t)
   (p:c9 (Fin n) K) :constant K n t ht (jet K n t p)=vh p:=rfl
theorem b62 (K:Type*) [cy K] (n t:ℕ) (ht:0<t) :
  pz (constant K n t ht)=aug K n t:= by
 ext x
 obtain ⟨p,rfl⟩:=qG x
 rw [u8 ,dO7,← u8 ,ker_constantCoeff]
 change p∈Vars K n↔p∈(aug K n t).comap (jet K n t)
 rw [x7 _ qG]
 change p∈Vars K n↔p∈Vars K n ⊔ pz (jet K n t)
 rw [uh,sup_eq_left.mpr (y5 ht.ne')]
@[simp] theorem bYD (K:Type*) [cy K] (n t:ℕ) (ht:0<t)
   (c:K) :constant K n t ht (aU K (gQ K n t) c)=c:= by
  change constant K n t ht (jet K n t (C c))=c
  simp
theorem dPb (K:Type*) [cy K] (n t:ℕ) (ht:0<t) :
   p7 (constant K n t ht) := fun c =>
 ⟨aU K (gQ K n t) c,bYD K n t ht c⟩
end
end aRV
end
section
namespace aA4
open Ideal
private theorem eEb {R:Type*} [cy R] (I:lV R) (a x :R)
    (hreg : ∀ y,a*y∈I→y∈I) :
    a*x∈I ⊔ span {a^2} ↔ x∈I ⊔ span {a} := by
  constructor
  · intro h
    obtain ⟨u,hu,v,hv,huv⟩:=Submodule.mem_sup.mp h
    obtain ⟨r,rfl⟩:=mem_span_singleton.mp hv
    have he :a*(x-a*r)=u:= by
      calc
        a*(x-a*r)=a*x-a^2*r := by ring
        _=u:= by rw [← huv,add_sub_cancel_right]
    exact Submodule.mem_sup.mpr
      ⟨x-a*r,hreg _ (he ▸ hu),a*r,mem_span_singleton.mpr ⟨r,rfl⟩,
        sub_add_cancel _ _⟩
  · intro h
    obtain ⟨u,hu,v,hv,rfl⟩:=Submodule.mem_sup.mp h
    obtain ⟨r,rfl⟩:=mem_span_singleton.mp hv
    exact Submodule.mem_sup.mpr
      ⟨a*u,I.mul_mem_left _ hu,a^2*r,mem_span_singleton.mpr ⟨r,rfl⟩,
        by rw [mul_add,pow_two,oY]⟩
theorem gup {k R:Type*} [Field k] [cy R] [oK k R]
    (I:lV R) (a :R) (hreg : ∀ y,a*y∈I→y∈I)
    [t5 k (R ⧸ (I ⊔ span {a}))] :
    t5 k (R ⧸ (I ⊔ span {a^2})) ∧
      u9 k (R ⧸ (I ⊔ span {a^2})) =
        2*u9 k (R ⧸ (I ⊔ span {a})) := by
  let J:lV R:=I ⊔ span {a}
  let J₂:lV R:=I ⊔ span {a^2}
  change t5 k (R ⧸ J₂)∧u9 k (R ⧸ J₂)=2*u9 k (R ⧸ J)
  have hle :J₂≤J:=sup_le_sup_left
    (span_singleton_le_span_singleton.mpr (dvd_pow_self a (by decide))) I
  let π: (R ⧸ J₂) →ₗ[k] (R ⧸ J) :=(Ideal.Quotient.factorₐ k hle).toLinearMap
  have hπ:p7 π:=Ideal.Quotient.factor_surjective hle
  let m:R →ₗ[k] (R ⧸ J₂) :=
    (Ideal.Quotient.mkₐ k J₂).toLinearMap.comp (LinearMap.mulLeft k a)
  let Jk :uz k R:=J.restrictScalars k
  have hm (x :R) :m x=0↔x∈J:= by
    change n5 J₂ (a*x)=0↔x∈J
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact eEb I a x hreg
  let ι: (R ⧸ J) →ₗ[k] (R ⧸ J₂) :=
    Jk.liftQ m (fun x hx=>LinearMap.mem_ker.mpr ((hm x).mpr hx))
  have hι (x :R) :ι (n5 J x)=n5 J₂ (a*x) :=rfl
  have hinj:qM ι:= by
    rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x,rfl⟩:=qG z
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hm x).mp (LinearMap.mem_ker.mp hz))
  have hexact :p6 ι π:= by
    rw [xu]
    ext z
    constructor
    · intro hz
      obtain ⟨x,rfl⟩:=qG z
      have hx :x∈J:=Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hz)
      obtain ⟨u,hu,v,hv,huv⟩:=Submodule.mem_sup.mp hx
      obtain ⟨r,rfl⟩:=mem_span_singleton.mp hv
      refine ⟨n5 J r,?_⟩
      rw [hι,← huv,map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr ((show I≤J₂ from vw) hu),
        zero_add]
    · rintro ⟨z,rfl⟩
      obtain ⟨x,rfl⟩:=qG z
      rw [hι]
      apply LinearMap.mem_ker.mpr
      change n5 J (a*x)=0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show span {a} ≤ J from le_sup_right) (mem_span_singleton.mpr ⟨x,rfl⟩))
  have hfin:t5 k (R ⧸ J₂) :=Module.Finite.of_exact hexact hπ
  refine ⟨hfin,?_⟩
  have hlen:=π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ,finrank_top,LinearMap.exact_iff.mp hexact,
    LinearMap.finrank_range_of_inj hinj] at hlen
  simpa only [two_mul] using hlen.symm
end aA4
end
section
namespace axh
noncomputable section
open MvPolynomial
variable {F L:Type*} [Field F] [Field L] [oK F L]
private def project (φ:L →ₗ[F] F) (P:c9 (Fin 3) L) :
  c9 (Fin 3) F :=
 AddMonoidAlgebra.ofCoeff (Finsupp.mapRange φ (oq φ) P.coeff)
private theorem bXT (φ:L →ₗ[F] F) (P:c9 (Fin 3) L)
  (m:Fin 3 →₀ ℕ) : (project φ P).coeff m=φ (P.coeff m) :=
 Finsupp.mapRange_apply (hf :=oq φ)
private theorem c5z (φ:L →ₗ[F] F) (P:c9 (Fin 3) F)
  (V:c9 (Fin 3) L) :
  project φ (oj (aU F L) P*V)=P*project φ V:= by
 ext m
 simp only [bXT,coeff_mul,coeff_map,oz]
 refine pQ rfl fun z _ => ?_
 rw [← Algebra.smul_def,t7,smul_eq_mul]
private theorem ePh (φ:L →ₗ[F] F) (V:c9 (Fin 3) L) :
  (project φ V).totalDegree≤V.totalDegree := by
 refine Finset.sup_le fun m hm=>th ?_
 rw [MvPolynomial.mem_support_iff,bXT] at hm
 exact MvPolynomial.mem_support_iff.mpr fun h=>hm (by rw [h,oq])
theorem fVP (P Q:c9 (Fin 3) F)
   (hP:P≠0) (hQ:Q≠0) (hrel :IsRelPrime P Q) :
   IsRelPrime (oj (aU F L) P)
     (oj (aU F L) Q) := by
 let i:=aU F L
 have hi:qM i:=i.injective
 have hmap :qM (oj (σ:=Fin 3) i) :=MvPolynomial.map_injective _ hi
 rintro D ⟨U,hU⟩ ⟨V,hV⟩
 by_contra hD
 have hv :V≠0:= by
   intro hz
   exact hQ (hmap (by rw [hV,hz,mul_zero,oq]))
 have hd:D ≠0:= by
   intro hz
   exact hP (hmap (by rw [hU,hz,zero_mul,oq]))
 have hdeg:0<D.totalDegree := by
   by_contra! h
   have hc:D =C (D.coeff 0) :=totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
   have hn:D.coeff 0≠0:= by
     intro hz
     exact hd (by rw [hc,hz,oq])
   exact hD (hc ▸ (isUnit_iff_ne_zero.mpr hn).map C)
 obtain ⟨m,hm⟩:=support_nonempty.mpr hv
 obtain ⟨φ,hφ⟩:=Module.Projective.exists_dual_ne_zero F (MvPolynomial.mem_support_iff.mp hm)
 have hpv :project φ V≠0:= fun h=>hφ (by
   simpa [bXT] using nI (fun G:c9 (Fin 3) F=>G.coeff m) h)
 have hsyzygy :P*project φ V= Q*project φ U:= by
   rw [← c5z,← c5z]
   change project φ (oj i P*V)=project φ (oj i Q*U)
   rw [hU,hV,oY ,oY ,mul_comm U V]
 have hdiv :Q∣project φ V :=
   hrel.symm.dvd_of_dvd_mul_left ⟨project φ U,hsyzygy⟩
 have hle :=(totalDegree_le_of_dvd_of_isDomain hdiv hpv).trans (ePh φ V)
 have heq :Q.totalDegree=D.totalDegree+V.totalDegree := by
   change (Finset.sup Q.support _)= _
   rw [← support_map_of_injective Q hi]
   change (oj i Q).totalDegree= _
   rw [hV,totalDegree_mul_of_isDomain hd hv]
 omega
end
end axh
end
section
namespace aY2
noncomputable section
open scoped BigOperators
open LinearMap Submodule
section Length
variable {R:Type*} [cy R]
private theorem be6 (S K:Type*) [cy S] [cy K]
    [oK R S] [oK K S] [Module.Flat R S]
    (I Q:lV R) (x :R)
    (hQ: (⊥ : uz R (R ⧸ I)).colon {I.mkQ x} = Q) :
    lI K (S ⧸ I.map (aU R S)) =
      lI K (S ⧸ Q.map (aU R S)) +
        lI K (S ⧸ (I ⊔ lz {x}).map (aU R S)) := by
  let N :=I ⊔ lz {x}
  let f₀:=toSpanSingleton R (R ⧸ I) (I.mkQ x)
  have hf₀:ker f₀= Q:= by
    rw [← hQ]
    ext a
    simp [f₀,mem_colon_singleton]
  let f : (R ⧸ Q) →ₗ[R] (R ⧸ I) := Q.liftQ f₀ hf₀.ge
  let hIN :I≤N :=vw
  let g: (R ⧸ I) →ₗ[R] (R ⧸ N) :=I.mapQ N LinearMap.id (by simpa using hIN)
  have hf :qM f :=
    ker_eq_bot.mp (Q.ker_liftQ_eq_bot f₀ hf₀.ge hf₀.le)
  have hg:p7 g:= by
    intro z
    obtain ⟨z,rfl⟩:=N.mkQ_surjective z
    exact ⟨I.mkQ z,rfl⟩
  have hfg:p6 f g:= by
    rw [xu]
    have hrange :lJ f=Submodule.map I.mkQ (lz {x}) := by
      dsimp only [f,f₀]
      rw [range_liftQ,LinearMap.range_toSpanSingleton,
        lz ,Submodule.map_span,p5]
    dsimp only [g]
    rw [ker_mapQ,comap_id,hrange]
    change Submodule.map I.mkQ ((I:uz R R) ⊔ lz {x})= _
    rw [Submodule.map_sup,mkQ_map_self,bot_sup_eq]
  let e (L:lV R) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S L).toLinearEquiv.restrictScalars K
  rw [(e I).length_eq,(e Q).length_eq,(e N).length_eq]
  exact wB ((f.baseChange S).restrictScalars K)
    ((g.baseChange S).restrictScalars K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (LinearMap.baseChange_surjective S hg) (Module.Flat.lTensor_exact S hfg)
def AN (I P:lV R) :ℕ∞ :=
  haveI:=Classical.dec P.IsPrime
  if hP:P.IsPrime then
    letI:=hP
    lI (oD P)
      (oD P ⧸ I.map (aU R (oD P)))
  else 0
theorem a5y (I P:lV R) [hp:P.IsPrime] :
    AN I P =
      lI (oD P)
        (oD P ⧸ I.map (aU R (oD P))) := by
  exact dite_eq_left hp
private theorem b78 {J I Q P:lV R} {x :R}
   (hJI:J≤I) (hP:J.IsMinimalPrime P) (hQ:Q.IsPrime)
   (hcolon : (⊥ : uz R (R ⧸ I)).colon {I.mkQ x} = Q) :
   AN I P=(if P= Q then 1 else 0)+AN (I ⊔ lz {x}) P:= by
 classical
 let hp:=hP.isPrime
 let L:=oD P
 have hIQ:I≤Q:= by
   intro y hy
   rw [← hcolon,mem_colon_singleton,Submodule.mem_bot]
   change y•n5 I x=0
   rw [Algebra.smul_def,Ideal.Quotient.algebraMap_eq,Ideal.Quotient.eq_zero_iff_mem.mpr hy,
     zero_mul]
 have hlen:=be6 L L I Q x hcolon
 rw [a5y,a5y,hlen]
 congr 1
 by_cases h:P= Q
 · rw [← h,ite_eq_left rfl,IsLocalization.AtPrime.map_eq_maximalIdeal P L]
   apply Module.length_eq_one_iff.mpr
   exact isSimpleModule_iff_quot_maximal.mpr
     ⟨_,IsLocalRing.maximalIdeal.isMaximal _,⟨LinearEquiv.refl _ _⟩⟩
 · have hn : ¬ Q≤P:= fun hQP=>h (hP.eq_of_le ⟨hQ,hJI.trans hIQ⟩ hQP).symm
   rw [ite_eq_right h,IsLocalization.AtPrime.map_eq_top_of_not_le (S:=L) hn]
   exact ze
theorem gMk (S K:Type*) [cy S] [cy K]
    [oK R S] [oK K S] [Module.Flat R S] [t6 R]
    (J:lV R) (uG:qx (lV R))
    (hmin : ∀ P∈uG,J.IsMinimalPrime P) :
    (∑ P∈uG,AN J P *
      lI K (S ⧸ P.map (aU R S))) ≤
      lI K (S ⧸ J.map (aU R S)) := by
  classical
  let d (I:lV R) :=lI K (S ⧸ I.map (aU R S))
  suffices H : ∀ I:lV R,J≤I→(∑ P∈uG,AN I P*d P)≤d I by
    exact H J le_rfl
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    intro hJI
    by_cases hI:I = ⊤
    · subst I
      have hw (P:lV R) (hP:P∈uG) :AN (⊤ : lV R) P=0:= by
        let hp:=(hmin P hP).isPrime
        rw [a5y,Ideal.map_top]
        exact ze
      simp [pQ rfl fun P hP=>show AN (⊤ : lV R) P*d P=0 by
        rw [hw P hP,zero_mul]]
    · have :vi (R ⧸ I) :=Submodule.Quotient.nontrivial_iff.mpr hI
      obtain ⟨Q,hQ⟩:=associatedPrimes.nonempty R (R ⧸ I)
      rw [AssociatedPrimes.mem_iff,isAssociatedPrime_iff] at hQ
      obtain ⟨hQ,z,hcolon⟩:=hQ
      obtain ⟨x,rfl⟩:=I.mkQ_surjective z
      have hx :x∉I:= by
        intro hx
        have hzero :I.mkQ x=0:=(Submodule.Quotient.mk_eq_zero I).mpr hx
        rw [hzero,Submodule.colon_singleton_zero] at hcolon
        exact hQ.ne_top hcolon
      let N :=I ⊔ lz {x}
      have hxN :x∈N :=
        (show lz {x} ≤ N from le_sup_right) (Ideal.mem_span_singleton_self x)
      have hIN :I<N :=t8 vw (fun he=>hx (he.symm ▸ hxN))
      have hnext:=ih N hIN (hJI.trans hIN.le)
      have hstep:d I=d Q+d N :=be6 S K I Q x hcolon.symm
      have hfirst :
          (∑ P∈uG,(if P= Q then (1 :ℕ∞) else 0)*d P)≤d Q:= by
        simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq']
        split <;> simp
      rw [hstep]
      calc
        _=(∑ P∈uG,(if P= Q then (1 :ℕ∞) else 0)*d P) +
              ∑ P∈uG,AN N P*d P:= by
          rw [← Finset.sum_add_distrib]
          apply pQ rfl
          intro P hP
          rw [b78 hJI (hmin P hP) hQ hcolon.symm,add_mul]
        _≤d Q+d N :=add_le_add hfirst hnext
end Length
end
end aY2
end
section
namespace bzH
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Polynomial
private theorem eDR {A:Type*} [cy A] [IsReduced A]
    {F g:A[X]} (hF:F.Monic) {n:ℕ} (h:F∣g^n) :
    F∣F.derivative*g:= by
  classical
  apply (modByMonic_eq_zero_iff_dvd hF).mp
  ext i
  rw [vl]
  apply (nilpotent_iff_mem_prime.mpr ?_).eq_zero
  intro P hP
  let:P.IsPrime :=hP
  let L:=FractionRing (A ⧸ P)
  let ρ:A →+* L:=(aU (A ⧸ P) L).comp (n5 P)
  have hFL: (F.map ρ).Monic:=hF.map ρ
  have hd:F.map ρ∣(g.map ρ)^n:= by
    simpa only [pU,coe_mapRingHom] using map_dvd (v9 ρ) h
  have hr :radical (F.map ρ)∣g.map ρ :=
    (exists_dvd_pow_iff_radical_dvd hFL.ne_zero).mp ⟨n,hd⟩
  have hL:F.map ρ∣(F.map ρ).derivative*g.map ρ:= by
    calc
      F.map ρ=EuclideanDomain.divRadical (F.map ρ)*radical (F.map ρ) :=
        EuclideanDomain.divRadical_mul_radical.symm
      _∣(F.map ρ).derivative*g.map ρ:=mul_dvd_mul (divRadical_dvd_derivative _) hr
  have hm: ((F.derivative*g) %ₘ F).map ρ=0:= by
    rw [map_modByMonic ρ hF,yJ,← derivative_map]
    exact (modByMonic_eq_zero_iff_dvd hFL).mpr hL
  have hc:=nI (fun p:L[X]=>p.coeff i) hm
  rw [coeff_map,vl] at hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (IsFractionRing.injective (A ⧸ P) L (by simpa [ρ] using hc))
attribute [local instance] Polynomial.algebra
theorem dLw {A:Type*} [cy A] (F g:A[X]) {q:A}
    (hq: (lz ({q} : Set A)).IsRadical) {n:ℕ}
    (hn:g^n∈lz {F,nq q}) :
    ∃ k :ℕ,nq F.leadingCoeff^k*(F.derivative*g) ∈
      lz {F,nq q} := by
  let I:lV A:=lz {q}
  let J:lV A[X] :=lz {F,nq q}
  let B:=A ⧸ I
  let a :B:=n5 I F.leadingCoeff
  let D:=zc a
  let π:A[X] →+* B[X] :=v9 (n5 I)
  let j:B[X] →+* D[X] :=aU B[X] D[X]
  let φ:A →+* D:=(aU B D).comp (n5 I)
  let:qy ((sS a).map (nq:B →+* B[X])) D[X] :=
    Polynomial.isLocalization (sS a) D
  have :IsReduced D:= by
    have hB: (⊥ : lV B).radical = ⊥ :=
      nilradical_eq_bot_iff.mpr ((Ideal.isRadical_iff_quotient_reduced I).mp hq)
    have hD:=IsLocalization.map_radical (sS a) D (⊥ : lV B)
    rw [hB,Ideal.map_bot] at hD
    exact nilradical_eq_bot_iff.mp hD.symm
  have hπ:p7 π :=
    Polynomial.map_surjective _ qG
  have hker :pz π=lz {nq q} := by
    change pz (v9 (n5 I))= _
    rw [Polynomial.ker_mapRingHom,uh]
    simp [I,pC]
  have hπq:π (nq q)=0:= by
    change (nq q).map (n5 I)=0
    rw [Polynomial.map_C,Ideal.Quotient.mk_singleton_self,Polynomial.C_0]
  have hJπ:J.map π=lz {π F} := by
    change (lz {F,nq q}).map π= _
    rw [Ideal.span_insert,Ideal.map_sup,pC,pC,
      p5 ,p5 ,hπq,Ideal.span_singleton_zero,sup_bot_eq]
  have hj (x :A[X]) :j (π x)=x.map φ:= by
    change (x.map (n5 I)).map (aU B D)= _
    rw [Polynomial.map_map]
  have hu:oZ (φ F.leadingCoeff) :=
    IsLocalization.Away.algebraMap_isUnit a
  have hlead: (F.map φ).leadingCoeff=φ F.leadingCoeff := by
    rcases subsingleton_or_nontrivial D with hD | hD
    · exact Subsingleton.elim _ _
    · exact leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero
  have hinv :φ F.leadingCoeff*(↑(hu.unit⁻¹) :D)=1 := by
    calc
      _=(↑hu.unit :D)*(↑(hu.unit⁻¹) :D) :=
        nI (fun c:D =>c*(↑(hu.unit⁻¹) :D)) hu.unit_spec.symm
      _=1 :=Units.mul_inv _
  let G:D[X] :=F.map φ*nq (↑(hu.unit⁻¹) :D)
  have hG:G.Monic:= by
    apply monic_mul_C_of_leadingCoeff_mul_eq_one
    exact hlead.symm ▸ hinv
  have hscale :G*nq (φ F.leadingCoeff)=F.map φ:= by
    dsimp only [G]
    rw [oY ,← mD,mul_comm (↑(hu.unit⁻¹) :D),hinv,map_one,mul_one]
  have hnπ:π F∣(π g)^n:= by
    have h:=t4 π (show g^n∈J from hn)
    rwa [hJπ,zm,pU] at h
  have hnD:F.map φ∣(g.map φ)^n:= by
    have h:=map_dvd j hnπ
    rwa [pU,hj,hj] at h
  have hd:=eDR hG
    ((show G∣F.map φ from ⟨_,hscale.symm⟩).trans hnD)
  have hderiv :G.derivative*nq (φ F.leadingCoeff) =
      (F.map φ).derivative := by
    simpa only [derivative_mul,derivative_C,mul_zero,add_zero]
      using nI derivative hscale
  have hdD:F.map φ∣(F.derivative*g).map φ:= by
    obtain ⟨d,hd⟩:=hd
    refine ⟨d,?_⟩
    rw [yJ,← derivative_map,← hderiv,mul_right_comm,hd,mul_right_comm,hscale]
  have hmem:j (π (F.derivative*g))∈(lz {π F}).map j:= by
    rw [pC,p5 ,zm,hj,hj]
    exact hdD
  obtain ⟨m,hm,hmJ⟩:=(vZ
    ((sS a).map (nq:B →+* B[X])) D[X] _ _).mp hmem
  obtain ⟨b,hb,rfl⟩:=hm
  obtain ⟨k,rfl⟩:=hb
  refine ⟨k,?_⟩
  have hkerle :pz π≤J:= by
    rw [hker,zk]
    apply xW
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hcomap : (J.map π).comap π=J:= by
    rw [x7 π hπ,← RingHom.ker_eq_comap_bot,sup_eq_left.mpr hkerle]
  rw [← show J=lz {F,nq q} from rfl,← hcomap,Ideal.mem_comap,hJπ]
  simpa only [mD,pU,π,coe_mapRingHom,Polynomial.map_C,a] using hmJ
end
end bzH
end
section
namespace bap
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem ew4 {R β:Type*} [cy R] (s :qx β)
    (w:β→R) (b:β) (hb:b∈s) (hu:oZ (w b)) (p:c9 β R)
    (hp:p*(∑ j∈s,C (w j)*X j)=0) :p=0:= by
  classical
  let e :=(renameEquiv R (qz b).symm).trans
    (uJ R {j // j≠b})
  have hc (r :R) :e (C r)=nq (C r) := by
    simp [e,xI,optionEquivLeft_C]
  have hx (j:β) : (e (X j)).coeff 1=if j=b then 1 else 0:= by
    by_cases hj:j=b
    · subst j
      simp [e,xI,optionEquivLeft_X_none]
    · simp [e,xI,yl hj,
        optionEquivLeft_X_some,hj]
  have hcoef : (e (∑ j∈s,C (w j)*X j)).coeff 1=C (w b) := by
    simp only [oz ,mD,Polynomial.finsetSum_coeff,hc,wY ,hx]
    rw [Finset.sum_eq_single_of_mem b hb]
    · simp
    · intro j _ hj
      simp [hj]
  have hregular :e (∑ j∈s,C (w j)*X j) ∈
      (vk (c9 {j // j≠b} R))⁰ :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
      (hcoef ▸ (hu.map (C (σ := {j // j≠b}))).mem_nonZeroDivisors)
  apply e.injective
  rw [oq,← mul_right_mem_nonZeroDivisors_eq_zero_iff hregular,← mD,hp,oq]
private theorem dEl {R α β:Type*} [cy R] (l:c9 α R)
  (s :qx β) (w:β→R) (b:β) (hb:b∈s) (hu:oZ (w b))
  (p:c9 β (c9 α R))
  (hp:p*(∑ j∈s,C (C (w j))*X j)∈lz {C l}) :
  p∈lz {C l} := by
 let I:lV (c9 α R) :=lz {l}
 let q:=n5 I
 have hk :pz (oj (σ:=β) q)=lz {C l} := by
  rw [MvPolynomial.ker_map,uh,pC,p5]
 have hmul :=RingHom.mem_ker.mp (hk.symm ▸ hp)
 rw [mD,oz] at hmul
 simp only [mD,xm,xL] at hmul
 rw [← hk,u8]
 exact ew4 s (fun j=>q (C (w j))) b hb ((hu.map C).map q) _ hmul
theorem dEg {R α β:Type*} [cy R] (l:c9 α R)
  (s :qx β) (w:β→R) (b:β) (hb:b∈s) (a :R)
  (p:c9 β (c9 α R))
  (hp:p*(∑ j∈s,C (C (w j))*X j)∈lz {C l}) :
  ∃ n:ℕ,(C (C (a*w b)))^n*p∈lz {C l} := by
 let z :=a*w b
 let T:=zc z
 let q:=aU R T
 let B:=c9 β (c9 α T)
 let M:=((sS z).map (C (σ:= α))).map (C (σ:=β))
 let g:=aU (c9 β (c9 α R)) B
 have hloc:qy M B:=MvPolynomial.isLocalization _ _
 have hu:oZ (q (w b)) := by
  have hz :oZ (q z) :=t3 T ⟨z,Submonoid.mem_powers _⟩
  change oZ (q (a*w b)) at hz
  rw [mD] at hz
  exact isUnit_of_mul_isUnit_right hz
 have hmap : (lz {C l}).map g=lz {C (oj q l)} := by
  rw [pC,p5]
  change lz {oj (oj q) (C l)} = _
  rw [xm]
 have hmem:=t4 g hp
 rw [hmap,mD] at hmem
 change g p*oj (oj q) (∑ j∈s,C (C (w j))*X j)∈_ at hmem
 simp only [oz ,mD,xm,xL] at hmem
 have h:=dEl (oj q l) s (q ∘ w) b hb hu (g p) hmem
 rw [← hmap] at h
 obtain ⟨d,hd,hdp⟩:=(vZ M B
  (lz {C l}) p).mp h
 obtain ⟨e,he,rfl⟩:=Submonoid.mem_map.mp hd
 obtain ⟨f,hf,rfl⟩:=Submonoid.mem_map.mp he
 obtain ⟨n,rfl⟩:=Submonoid.mem_powers_iff _ _ |>.mp hf
 exact ⟨n,by simpa only [pU] using hdp⟩
theorem dEi {A B:Type*} [cy A] [cy B] [oK A B]
   (M:Submonoid A) [qy M B] (I:lV A) (z r :A)
   (h : ∀ p:A,p*r∈I → ∃ n:ℕ,z^n*p∈I)
   (q:B) (hq:q*aU A B r∈I.map (aU A B)) :
   ∃ n:ℕ,(aU A B z)^n*q∈I.map (aU A B) := by
 obtain ⟨⟨p,s⟩,hs⟩:=IsLocalization.surj M q
 have hp:aU A B (p*r)∈I.map (aU A B) := by
   rw [mD,← hs]
   have hmul :aU A B s*(q*aU A B r)∈I.map (aU A B) :=
     Ideal.mul_mem_left _ _ hq
   convert hmul using 1
   ac_rfl
 obtain ⟨d,hd,hdp⟩:=(vZ M B I _).mp hp
 rw [← oY] at hdp
 obtain ⟨n,hn⟩:=h (d*p) hdp
 refine ⟨n,?_⟩
 have he :=t4 (aU A B) hn
 rw [mD,pU,mD,← hs] at he
 have hu:=(t3 B ⟨d,hd⟩).mul (t3 B s)
 have he' : (aU A B d*aU A B s)*((aU A B z)^n*q) ∈
     I.map (aU A B) := by
   convert he using 1
   ac_rfl
 exact (Ideal.unit_mul_mem_iff_mem _ hu).mp he'
end
end bap
end
