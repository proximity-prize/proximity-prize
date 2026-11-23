import ProximityPrize.SubmissionLower.Zg1hxlb
import ProximityPrize.SubmissionLower.ZqSpAfd
import ProximityPrize.SubmissionLower.ZwLbCYa
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, Module.Finite → zAa, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.map_injective → zTo, Polynomial.ringHom_ext → z86, RingHom.comp_assoc → zxS, RingHom.ext → zz4, RingHom.ker → zdq
section
section
set_option backward.isDefEq.respectTransparency false
namespace qNm1sVb
noncomputable section
open Polynomial qThdpma
open qNu3xvc (Equation EC a7W seed amm jU KM chartEq polar)
open qdpQ3Rb (AffinePencil numerator)
open scoped nonZeroDivisors
variable {E :Type} [Field E]
private theorem root_pair (A:Equation E) :
  pairHom (seed A) (amm A) (jU A false)=a7W A:= by
 have h:eval₂RingHom (seed A) (amm A)=(a7W A).comp C:= by
  apply z86
  · simp [seed]
  · simp [amm]
 unfold pairHom
 rw [h]
 apply z86 <;> simp [jU]
private theorem chart_root (A:Equation E) :KM A false=a7W A:= by
 apply z86 <;> simp [KM,jU]
variable [Algebra cu.L E]
private theorem pair_surjective {A:Equation E} (D:AffinePencil A) :
   letI:=D.base.toAlgebra
   Function.Surjective (pairHom D.base (amm A) (jU A false)) := by
 let J:=RatFunc E
 let F:=EC A
 let:Algebra J F:=D.base.toAlgebra
 let:zAa J F:=D.finite
 let k :=pairHom D.base (amm A) (jU A false)
 let S:Subalgebra J F :=
   { k.rangeS with
     algebraMap_mem' := fun a=>⟨C (C a),by simp [k,pairHom]; rfl⟩ }
 let lift:=pairHom (C.comp (C.comp (RatFunc.C:E →+* J)))
   (C (z7y:J[X])) (z7y:J[X][X])
 have hC:k.comp (C.comp (C.comp (RatFunc.C:E →+* J)))=seed A:= by
   apply zz4
   intro a
   simpa [k,pairHom] using D.base_seed a
 have hm (b:AdjoinRoot A.f) :algebraMap (AdjoinRoot A.f) F b∈S:= by
   obtain ⟨g,rfl⟩:=AdjoinRoot.mk_surjective b
   refine ⟨lift g,?_⟩
   change k (lift g)=a7W A g
   unfold lift
   rw [pair_map,hC]
   have hx :k (C (z7y:J[X]))=amm A:= by simp [k,pairHom]
   have hy :k (z7y:J[X][X])=jU A false := by simp [k,pairHom]
   rw [hx,hy,root_pair]
 intro a
 change a∈S
 obtain ⟨b,c,_,rfl⟩:=IsFractionRing.div_surjective (AdjoinRoot A.f) a
 rw [div_eq_mul_inv]
 exact S.mul_mem (hm b) ((Algebra.IsIntegral.isIntegral (R:=J) _).inv_mem (hm c))
private theorem value_power {J F:Type} [Field J] [Field F] [Algebra J F]
   [zAa J F] (B:PowerBasis J F) (Q:J[X]) :
   (multMatrix (minpoly J B.gen).natDegree (minpoly J B.gen) Q).charpoly =
     (Algebra.lmul J F (aeval B.gen Q)).charpoly := by
 classical
 rw [B.natDegree_minpoly,← LinearMap.charpoly_toMatrix _ B.basis,
   ← Algebra.leftMulMatrix_apply]
 congr 1
 ext i j
 let p:= Q*(z7y:J[X])^(j:ℕ)
 have h:=congrArg (aeval B.gen) (sum_modByMonic_coeff (p:=p)
   (minpoly.monic B.isIntegral_gen) (n:=B.dim) (by rw [B.degree_minpoly]))
 have hsum: (∑ k :Fin B.dim,((p %ₘ minpoly J B.gen).coeff k)•B.basis k) =
     aeval B.gen Q*B.basis j:= by
   simpa only [map_sum,aeval_monomial,minpoly.aeval_modByMonic_minpoly,Algebra.smul_def,
     B.basis_eq_pow,p,map_mul,map_pow,aeval_X] using h
 rw [Algebra.leftMulMatrix_eq_repr_mul,← hsum,B.basis.repr_sum_self]
 rfl
theorem proof :qThdpma.c1 := by
  intro E _ _ A D hj
  let J:=RatFunc E
  let F:=EC A
  let:Algebra J F:=D.base.toAlgebra
  let:zAa J F:=D.finite
  let:Algebra.IsSeparable J F:=D.separable
  let B:=Field.powerBasisOfFiniteOfSeparable J F
  let ev :=(aeval (R:=J) B.gen).toRingHom
  let g:=numerator A D.a D.b D.c
  let q:=polar A false
  let jac:=cutJac (seed A) (amm A) (jU A false) (D.base RatFunc.X) A.f g
  have hC:ev.comp C=D.base :=zz4 fun a=>aeval_C B.gen a
  have hseed :ev.comp (C.comp RatFunc.C)=seed A:= by
    rw [← zxS,hC]
    exact zz4 D.base_seed
  obtain ⟨x,hx⟩:=B.exists_eq_aeval' (amm A)
  obtain ⟨y,hy⟩:=B.exists_eq_aeval' (jU A false)
  obtain ⟨qi,hqi⟩:=B.exists_eq_aeval' q⁻¹
  obtain ⟨ji,hji⟩:=B.exists_eq_aeval' jac⁻¹
  obtain ⟨r,hr⟩:=pair_surjective D B.gen
  have hx' : ev x=amm A:=hx.symm
  have hy' : ev y=jU A false :=hy.symm
  have hu:ev (C (RatFunc.X:J))=D.base RatFunc.X:=RingHom.congr_fun hC _
  have he (p:E[X][X]) :ev (pairHom (C.comp RatFunc.C) x y p)=a7W A p:= by
    rw [pair_map,hseed,hx',hy',root_pair]
  have hq:a7W A A.f.derivative=q:= by
    simp [q,polar,chartEq,chart_root]
  have hg:a7W A g=D.base RatFunc.X*q:= by
    have h:D.base RatFunc.X=KM A false g/q:=D.base_X
    rw [chart_root] at h
    exact ((eq_div_iff D.polar_ne).mp h).symm
  let M:FibreModel RatFunc.C RatFunc.X D :=
    { P:=minpoly J B.gen
      monic:=minpoly.monic B.isIntegral_gen
      separable :=Algebra.IsSeparable.isSeparable J B.gen
      x :=x
      y :=y
      recover :=r
      qInv :=qi
      jacInv :=ji
      f_dvd:=minpoly.dvd J B.gen (show ev _=0 by rw [he]; simp [a7W])
      cut_dvd:=minpoly.dvd J B.gen (show ev _=0 by
        rw [map_sub,map_mul,hu,he,he,hq,hg,sub_self])
      polar_dvd:=minpoly.dvd J B.gen (show ev _=0 by
        rw [map_sub,map_mul,map_one,he,hq,show ev qi=q⁻¹ from hqi.symm,
          mul_inv_cancel₀ D.polar_ne,sub_self])
      jac_dvd:=minpoly.dvd J B.gen (show ev _=0 by
        rw [map_sub,map_mul,map_one,jac_map,hseed,hx',hy',hu]
        change jac*ev ji - 1=0
        rw [show ev ji=jac⁻¹ from hji.symm,mul_inv_cancel₀ hj,sub_self])
      recover_dvd:=minpoly.dvd J B.gen (show ev _=0 by
        rw [map_sub,pair_map,hC,hx',hy',hr]
        change B.gen-aeval B.gen (z7y:J[X])=0
        rw [aeval_X,sub_self]) }
  refine ⟨M,?_⟩
  change (multMatrix (minpoly J B.gen).natDegree (minpoly J B.gen) M.polar).charpoly =
    (Algebra.lmul J F q).charpoly
  rw [value_power B,show aeval B.gen M.polar=q from (he _).trans hq]
end
end qNm1sVb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qty7P2c
noncomputable section
open Polynomial
open qThdpma
open private genericCoeff_poly matrix_map from ProximityPrize.SubmissionLower.ZqSpAfd
theorem proof :qThdpma.c2 := by
  classical
  intro E _ _ A D M
  obtain ⟨a,b,hab⟩:=(separable_def' M.P).mp M.separable
  let polys :=M.recover.coeffs ∪ {M.P,M.x,M.y,M.qInv,M.jacInv,a,b}
  let V:=polys.biUnion Polynomial.coeffs
  let d:E[X] := ∏ t∈V,RatFunc.denom t
  have hd:d≠0:=Finset.prod_ne_zero_iff.mpr fun t _=>RatFunc.denom_ne_zero t
  let R:=Localization.Away d
  let l:E[X] →+* R:=algebraMap _ _
  let i:R →+* RatFunc E :=qY hd
  let k :=mapRingHom i
  have hi (f :E[X]) :i (l f)=algebraMap E[X] (RatFunc E) f :=genericCoeff_poly hd f
  have hinj:zq4 i:= by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers d) i).mpr
    intro f g
    change l f=l g↔i (l f)=i (l g)
    exact ⟨congrArg i,fun h=>congrArg l (RatFunc.algebraMap_injective E
      ((hi f).symm.trans (h.trans (hi g))))⟩
  have hcoeff (t:RatFunc E) (ht:t∈V) :t∈Set.range i:= by
    have hu:IsUnit (l t.denom) :=
      IsLocalization.Away.isUnit_of_dvd d (Finset.dvd_prod_of_mem RatFunc.denom ht)
    obtain ⟨v,hv⟩:=hu.exists_left_inv
    have hvi:i v=(i (l t.denom))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul,hv,map_one])
    exact ⟨l t.num*v,by rw [map_mul,hvi,hi,hi,← div_eq_mul_inv,RatFunc.num_div_denom]⟩
  have lower (p: (RatFunc E)[X]) (hp:p∈polys) : ∃ q:R[X],q.map i=p:= by
    apply (mem_lifts _).mp
    apply (lifts_iff_coeffs_subset_range _).mpr
    intro t ht
    exact hcoeff t (Finset.mem_biUnion.mpr ⟨p,hp,ht⟩)
  obtain ⟨P,hP⟩:=lower M.P (by simp [polys])
  obtain ⟨x,hx⟩:=lower M.x (by simp [polys])
  obtain ⟨y,hy⟩:=lower M.y (by simp [polys])
  obtain ⟨q,hq⟩:=lower M.qInv (by simp [polys])
  obtain ⟨J,hJ⟩:=lower M.jacInv (by simp [polys])
  obtain ⟨a',ha'⟩:=lower a (by simp [polys])
  obtain ⟨b',hb'⟩:=lower b (by simp [polys])
  have hrecover : ∃ f :R[X][X],f.map k=M.recover := by
    apply (mem_lifts _).mp
    apply (lifts_iff_coeffs_subset_range _).mpr
    intro p hp
    exact lower p (Finset.mem_union_left _ hp)
  obtain ⟨r,hr⟩:=hrecover
  have hm:P.Monic:=hinj.monic_map_iff.mpr (hP.symm ▸ M.monic)
  have hsep:P.Separable := by
    refine (separable_def' P).mpr ⟨a',b',map_injective i hinj ?_⟩
    simpa only [Polynomial.map_add,Polynomial.map_mul,← derivative_map,hP,ha',hb',
      Polynomial.map_one] using hab
  have hlocal:i.comp (bfj d)=RatFunc.C:= by
    apply zz4
    intro c
    change i (l (z1z c))=RatFunc.C c
    rw [hi,RatFunc.algebraMap_C]
  have hC:k.comp (Polynomial.C.comp (bfj d))=Polynomial.C.comp RatFunc.C:= by
    rw [← zxS,mapRingHom_comp_C,zxS,hlocal]
  have hu:k (z1z (localParameter d))=z1z (RatFunc.X:RatFunc E) := by
    have h:i (localParameter d)=RatFunc.X:=(hi z7y).trans RatFunc.algebraMap_X
    rw [show k (z1z (localParameter d)) =
      z1z (i (localParameter d)) from map_C i,h]
  have hpair (f :E[X][X]) :
      k (pairHom (Polynomial.C.comp (bfj d)) x y f) =
        pairHom (Polynomial.C.comp RatFunc.C) M.x M.y f := by
    rw [pair_map,hC]
    change pairHom _ (x.map i) (y.map i) f= _
    rw [hx,hy]
  have hjac (f g:E[X][X]) :
      k (cutJac (Polynomial.C.comp (bfj d)) x y (z1z (localParameter d)) f g) =
        cutJac (Polynomial.C.comp RatFunc.C) M.x M.y (z1z RatFunc.X) f g:= by
    rw [jac_map,hC,hu]
    change cutJac _ (x.map i) (y.map i) _ f g= _
    rw [hx,hy]
  have hrec:k (pairHom z1z x y r)=pairHom z1z M.x M.y M.recover := by
    rw [pair_map,mapRingHom_comp_C,← hr]
    change pairHom (Polynomial.C.comp i) (x.map i) (y.map i) r= _
    rw [hx,hy]
    simp only [pairHom,coe_eval₂RingHom,eval₂_map]
    congr 1
    exact zz4 fun p=>(eval₂_map i z1z M.x).symm
  have reflect {f :R[X]} (hf :M.P∣k f) :P∣f := by
    apply (map_dvd_map i hinj hm).mp
    rw [hP]
    exact hf
  let S:FibreModel (bfj d) (localParameter d) D :=
    { P:=P,monic:=hm,separable :=hsep,x :=x,y :=y,recover :=r,qInv :=q,jacInv :=J
      f_dvd:=reflect (by rw [hpair]; exact M.f_dvd)
      cut_dvd:=reflect (by
        rw [map_sub,map_mul,hu,hpair,hpair]
        exact M.cut_dvd)
      polar_dvd:=reflect (by
        simp only [map_sub,map_mul,hpair,show k q=M.qInv from hq,map_one]
        exact M.polar_dvd)
      jac_dvd:=reflect (by
        rw [map_sub,map_mul,hjac,show k J=M.jacInv from hJ,map_one]
        exact M.jac_dvd)
      recover_dvd:=reflect (by
        rw [map_sub,hrec,show k z7y=z7y from map_X i]
        exact M.recover_dvd) }
  refine ⟨d,hd,S,?_⟩
  have hPolar :S.polar.map i=M.polar :=hpair _
  have hdeg:P.natDegree=M.P.natDegree := by
    rw [← hP,hm.natDegree_map i]
  change (multMatrix P.natDegree P S.polar).charpoly.map i=M.value
  rw [← Matrix.charpoly_map,matrix_map i _ _ _ hm,hP,hPolar]
  exact congrArg (fun n=>(multMatrix n M.P M.polar).charpoly) hdeg
end
end qty7P2c
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qralmib
noncomputable section
open Polynomial
open scoped Classical WithZero
open cu (L)
open q1kuFjb (mapTwice)
open qLXroAb (dx)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private gauss₂ coeff_le_gauss₂ gauss₂_bound from ProximityPrize.SubmissionLower.ZhEC96c
open private chain₂ from ProximityPrize.SubmissionLower.Z5cOcra
variable {R T U:Type} [CommRing R] [CommRing T] [CommRing U]
theorem coeff_mapTwice (j:R →+* T) (f :R[X][X]) (i k :ℕ) :
  ((mapTwice j f).coeff i).coeff k=j ((f.coeff i).coeff k) := by
 simp [mapTwice]
def evalPair (j:R →+* T) (x y :T) :R[X][X] →+* T :=
 eval₂RingHom (eval₂RingHom j x) y
theorem evalPair_map (j:R →+* T) (k :T →+* U) (x y :U) (p:R[X][X]) :
  evalPair k x y (mapTwice j p)=evalPair (k.comp j) x y p:= by
 change (p.map (mapRingHom j)).eval₂ (eval₂RingHom k x) y =
  p.eval₂ (eval₂RingHom (k.comp j) x) y
 rw [eval₂_map]
 congr 1
 apply z86 <;> simp
theorem hom_evalPair (j:R →+* T) (k :T →+* U) (x y :T) (p:R[X][X]) :
  k (evalPair j x y p)=evalPair (k.comp j) (k x) (k y) p:= by
 change k (p.eval₂ (eval₂RingHom j x) y)=p.eval₂ (eval₂RingHom (k.comp j) (k x)) (k y)
 rw [hom_eval₂]
 congr 1
 apply z86 <;> simp
def D6 (f :R[X][X]) :R[X][X] :=
 f.sum fun i g=>monomial i g.derivative
theorem map_partialX (j:R →+* T) (f :R[X][X]) :
  mapTwice j (D6 f)=D6 (mapTwice j f) := by
 ext i k
 simp only [coeff_mapTwice,D6,sum_coeff derivative derivative_zero,coeff_derivative,
  map_mul,map_add,map_one,map_natCast]
theorem map_derivative (j:R →+* T) (f :R[X][X]) :
   mapTwice j f.derivative=(mapTwice j f).derivative :=
 (derivative_map f (mapRingHom j)).symm
theorem marked_partial (f :L[X][X]) (s :L[X])
   (h:evalPair C z7y s f=0) :
   -evalPair C z7y s (dx f)=evalPair C z7y s f.derivative*s.derivative := by
 let D:Derivation ℤ L[X] L[X] :=(Polynomial.derivative' (R:=L)).restrictScalars ℤ
 have hD (a :L) :D (C a)=C ((0:Derivation L L L) a) := by
   change (C a).derivative=C ((0:Derivation L L L) a)
   simp
 have hc:=chain₂ (0:Derivation L L L) D C hD z7y s f
 change (evalPair C z7y s f).derivative =
   evalPair C z7y s (qNu3xvc.seedDerivative 0 f) +
     evalPair C z7y s (dx f)*Polynomial.X.derivative +
     evalPair C z7y s f.derivative*s.derivative at hc
 have hz :qNu3xvc.seedDerivative 0 f=0:= by
   simp [qNu3xvc.seedDerivative,Polynomial.sum_def]
 simp only [h,hz,map_zero,zero_add,derivative_X,mul_one] at hc
 exact neg_eq_iff_add_eq_zero.mpr (by simpa only [add_comm] using hc.symm)
variable {E :Type} [Field E]
theorem liftIntegral (v :Valuation E ℤᵐ⁰) (f :E[X][X])
  (hf : ∀ i j,v ((f.coeff i).coeff j)≤1) :
  ∃ p:v.valuationSubring[X][X],mapTwice v.valuationSubring.toSubring.subtype p=f := by
 let i:=v.valuationSubring.toSubring.subtype
 apply (lifts_iff_set_range f).mp
 apply (lifts_iff_coeff_lifts f).mpr
 intro n
 apply (lifts_iff_set_range (f.coeff n)).mp
 apply (lifts_iff_coeff_lifts (f.coeff n)).mpr
 intro m
 exact ⟨⟨_,hf n m⟩,rfl⟩
theorem integralQuotient (v :Valuation E ℤᵐ⁰) (f g:E[X][X])
  (hn: (f.coeff f.natDegree).leadingCoeff=1)
  (h : ∀ i j,v (((f*g).coeff i).coeff j)≤1) :
  ∀ i j,v ((g.coeff i).coeff j)≤1 := by
 have h₁:1≤gauss₂ v f := by
  have hm:=coeff_le_gauss₂ v f f.natDegree (f.coeff f.natDegree).natDegree
  rwa [coeff_natDegree,hn,map_one] at hm
 have h₂:gauss₂ v (f*g)≤1 := by
  simpa using gauss₂_bound v (f*g) (b:=0) (by simpa [qFD8jve.aFA] using h)
 intro i j
 calc
  _≤gauss₂ v g:=coeff_le_gauss₂ v g i j
  _≤gauss₂ v f * gauss₂ v g:=le_mul_of_one_le_left zero_le h₁
  _≤1 := by rwa [← map_mul]
theorem mapTwice_injective (j:R →+* T) (hj:zq4 j) :
  zq4 (mapTwice j) :=
 zTo _ (zTo _ hj)
variable {M B:Type} [Field M] [Field B]
theorem localize (A:Subring M) (r :A →+* B) :
   ∃ (O:Subring M) (i:A →+* O) (red:O →+* B),
     (∀ a,(i a :M)=(a :M))∧(∀ a,red (i a)=r a) ∧
     ∀ a,red a≠0→ IsUnit a := by
 let P:=zdq r
 let:P.IsPrime :=RingHom.ker_isPrime r
 let O:=(LocalSubring.ofPrime A P).toSubring
 let i:=algebraMap A O
 have hU (s :P.primeCompl) :IsUnit (r s) :=
   isUnit_iff_ne_zero.mpr s.property
 let red:=IsLocalization.lift (S:=O) hU
 refine ⟨O,i,red,fun _=>rfl,IsLocalization.lift_eq hU,?_⟩
 intro a ha
 obtain ⟨b,s,rfl⟩:=IsLocalization.exists_mk'_eq P.primeCompl a
 apply (IsLocalization.AtPrime.isUnit_mk'_iff O P b s).mpr
 intro hb
 exact ha ((IsLocalization.lift_mk'_spec hU b 0 s).mpr (by
   rw [mul_zero]
   exact hb))
end
end qralmib
end
section
set_option backward.isDefEq.respectTransparency false
namespace qralmib
noncomputable section
open Polynomial
open scoped Classical WithZero
open P5 (K)
open cu (L FX j9)
open P5_7_7 (phys)
open qb0hmCe (cLN)
open q1kuFjb (mapTwice expansion_coeff)
open P5_7_3_5_2 (atPolynomial)
open qLXroAb (evalXY dx seedRing)
open q9uVqha (seedResidue seedResidue_apply)
private theorem phys_eval (g:L[X][X]) (s :K[X]) :
  phys (evalPair C z7y (j9 s) g)=atPolynomial g s := by
 have hid :eval₂RingHom C (z7y:L[X])=RingHom.id L[X] :=
  zz4 fun g=>eval₂_C_X
 change phys (g.eval₂ (eval₂RingHom C z7y) (j9 s))= _
 rw [hid,hom_eval₂,RingHom.comp_id]
 rfl
theorem proof :q9uVqha.c2 := by
  intro q Cq z S F V G γ hγ
  let h:=V.Bp hγ
  let w:=(F.place γ).value
  let i:=(seedRing F γ).subtype
  let a :=F.atPlace γ h
  let b:=seedResidue F γ h
  let s :=j9 (S γ)
  let j:=evalPair ((algebraMap Cq.E G.M).comp i) G.x G.y
  let k :=evalPair ((phys.comp C).comp b) (phys z7y) (phys s)
  obtain ⟨f,hf⟩:=liftIntegral w F.f (F.integral γ h)
  change mapTwice i f=F.f at hf
  have hg (p: (seedRing F γ)[X][X]) :
      j p=evalXY (mapTwice i p) G.x G.y :=
    (evalPair_map i (algebraMap Cq.E G.M) G.x G.y p).symm
  have hr :mapTwice b f=cLN a 0 F.f := by
    ext n m
    rw [coeff_mapTwice,expansion_coeff,← hf,coeff_mapTwice]
    exact seedResidue_apply γ h _
  have hk (p: (seedRing F γ)[X][X]) :
      k p=phys (evalPair C z7y s (mapTwice b p)) := by
    rw [evalPair_map,hom_evalPair]
    rfl
  have hroot :=F.root γ h
  have hsimple :=V.simple γ hγ
  change atPolynomial (cLN a 0 F.f) (S γ)=0 at hroot
  change atPolynomial (cLN a 0 F.f).derivative (S γ)≠0 at hsimple
  have hkf :k f=0:= by rw [hk,hr,phys_eval,hroot]
  have hkd:k f.derivative≠0:= by
    rwa [hk,map_derivative,hr,phys_eval]
  have hker :zdq j.rangeRestrict≤zdq k := by
    intro p hp
    have hpj:j p=0:=congrArg Subtype.val (RingHom.mem_ker.mp hp)
    rw [hg] at hpj
    obtain ⟨g,hg'⟩:=(G.kernel _).mp hpj
    have hint (n m:ℕ) :w (((F.f*g).coeff n).coeff m)≤1 := by
      rw [← hg',coeff_mapTwice]
      exact ((p.coeff n).coeff m).property
    obtain ⟨g',hgg⟩:=liftIntegral w g (integralQuotient w F.f g F.normalized hint)
    change mapTwice i g' = g at hgg
    have he :p=f * g' := mapTwice_injective i (Subring.subtype_injective _)
      (by rw [map_mul,hf,hgg,hg'])
    rw [RingHom.mem_ker,he,map_mul,hkf,zero_mul]
  let r :=(j.rangeRestrict.liftOfSurjective j.rangeRestrict_surjective) ⟨k,hker⟩
  obtain ⟨O,ι,red,hι,hred,hu⟩:=localize j.range r
  let u:=ι.comp j.rangeRestrict
  have huval (p: (seedRing F γ)[X][X]) : (u p:G.M)=j p:=hι _
  have hured (p: (seedRing F γ)[X][X]) :red (u p)=k p :=
    (hred _).trans (RingHom.liftOfSurjective_comp_apply _ _ _ p)
  let X₀:=u (C z7y)
  let Y₀:=u z7y
  let P:=u f.derivative
  let Q:=u (D6 f)
  have hX: (X₀:G.M)=G.x := by
    change (u (C z7y) :G.M)=G.x
    rw [huval]
    simp [j,evalPair]
  have hY: (Y₀:G.M)=G.y := by
    change (u z7y:G.M)=G.y
    rw [huval]
    simp [j,evalPair]
  have hXr :red X₀=phys Polynomial.X:= by
    change red (u (C z7y))= _
    rw [hured]
    simp [k,evalPair]
  have hYr :red Y₀=phys s := by
    change red (u z7y)= _
    rw [hured]
    simp [k,evalPair]
  have hP: (P:G.M)=evalXY F.f.derivative G.x G.y := by
    change (u f.derivative :G.M)= _
    rw [huval,hg,map_derivative,hf]
  have hQ: (Q:G.M)=evalXY (dx F.f) G.x G.y := by
    change (u (D6 f) :G.M)= _
    rw [huval,hg,map_partialX,hf]
    rfl
  have hPr :red P≠0:= by
    change red (u f.derivative)≠0
    rwa [hured]
  obtain ⟨e,he⟩:=(hu P hPr).exists_right_inv
  have heval : (e :G.M)=(evalXY F.f.derivative G.x G.y)⁻¹:= by
    have he' : (P:G.M)*(e :G.M)=1 :=congrArg Subtype.val he
    rw [hP] at he'
    exact eq_inv_of_mul_eq_one_right he'
  have hQr : -red Q=red P*phys s.derivative := by
    have h₀:evalPair C z7y s (mapTwice b f)=0:= by
      apply (IsFractionRing.injective L[X] FX)
      change phys (evalPair C z7y s (mapTwice b f))=phys 0
      rw [hr,phys_eval,hroot,map_zero]
    have hh:=congrArg phys (marked_partial _ s h₀)
    change -red (u (D6 f))=red (u f.derivative)*phys s.derivative
    rw [hured,hured,hk f.derivative,hk (D6 f),
      map_partialX,map_derivative]
    simpa only [map_neg,map_mul,D6,dx] using hh
  have her :red P*red e=1 := by
    simpa only [map_mul,map_one] using congrArg red he
  let t: (seedRing F γ) →+* O:=u.comp (C.comp C)
  let v :Fin 4→O := ![1,X₀,Y₀,-Q*e]
  refine ⟨⟨O,red,hu,t,?_,?_,v,?_,?_⟩⟩
  · intro c
    change (u (C (C c)) :G.M)=algebraMap Cq.E G.M (c:Cq.E)
    rw [huval]
    simp [j,evalPair,i]
  · intro c
    change red (u (C (C c)))= _
    rw [hured]
    simp [k,evalPair,b]
  · intro n
    fin_cases n
    · change (1 :G.M)=evalXY F.f.derivative G.x G.y /
        evalXY F.f.derivative G.x G.y
      exact (div_self G.polar_ne).symm
    · change (X₀:G.M)=G.x*evalXY F.f.derivative G.x G.y /
        evalXY F.f.derivative G.x G.y
      rw [hX,mul_div_cancel_right₀ _ G.polar_ne]
    · change (Y₀:G.M)=G.y*evalXY F.f.derivative G.x G.y /
        evalXY F.f.derivative G.x G.y
      rw [hY,mul_div_cancel_right₀ _ G.polar_ne]
    · change -(Q:G.M)*(e :G.M) = -evalXY (dx F.f) G.x G.y /
        evalXY F.f.derivative G.x G.y
      rw [hQ,heval,div_eq_mul_inv]
  · intro n
    fin_cases n
    · change red 1=phys 1
      rw [map_one,map_one]
    · exact hXr
    · exact hYr
    · change red (-Q*e)=phys s.derivative
      rw [map_mul,map_neg,hQr,mul_right_comm,her,one_mul]
end
end qralmib
end
section
set_option autoImplicit true
namespace qbeSBca
theorem proof :qJh2f6d.c2 :=qralmib.proof
end qbeSBca
end
section
namespace qXARP7c
noncomputable section
open Polynomial Finset
open scoped WithZero
open cu (L)
open E7 (KB)
open qLXroAb
theorem proof :qLXroAb.c7:= by
  classical
  intro q Cq z S F A w B R k hB hR hI hD hC
  let v :=baseVal w.value
  let j:=(algebraMap Cq.E (tu Cq.E)).comp (algebraMap L Cq.E)
  have hj (c:L) (hc:c≠0) :v (j c)=1 :=
    (base_const w.value _).trans (w.on_constants c hc)
  let s :=B.roots.toFinset
  have hroot (i:s) :B.eval (i:L)=0 :=
    (mem_roots hB).mp (Multiset.mem_toFinset.mp i.property)
  choose T hx hm using fun i:s=>hC (i:L) (hroot i)
  let a :=A.polar
  have ha :a≠0:=A.polar_ne
  have hunit (i:s) (c:L) (hc:c≠0) :
      (T i).value (algebraMap (tu Cq.E) A.M (j c))=1 := by
    rw [vertical_base,hj c hc,one_pow]
  have hconst (c:L) :algebraMap (tu Cq.E) A.M (j c) =
      algebraMap Cq.E A.M (algebraMap L Cq.E c) :=
    (IsScalarTower.algebraMap_apply Cq.E (tu Cq.E) A.M _).symm
  have hsep:Set.InjOn (fun i:s=>(T i).value) (Finset.univ :Finset s) := by
    intro i _ r _ hir
    change (T i).value=(T r).value at hir
    apply Subtype.ext
    by_contra hne
    have h₁: (T i).value (A.x-algebraMap (tu Cq.E) A.M (j i))<1 := by
      rw [hconst]; exact hx i
    have h₂: (T i).value (A.x-algebraMap (tu Cq.E) A.M (j r))<1 := by
      rw [hir,hconst]; exact hx r
    have h:=(T i).value.map_sub_lt h₂ h₁
    rw [sub_sub_sub_cancel_left,← map_sub (algebraMap (tu Cq.E) A.M),← j.map_sub,hunit i _ (sub_ne_zero.mpr hne)] at h
    exact lt_irrefl _ h
  let:=A.separable
  obtain ⟨c,hc,hb,hbI,hn⟩:=eFi v j hj a ha
  let b:=a/(algebraMap (tu Cq.E) A.M (j c)-a)
  have hsum:=integral_norm_order v (base_surj w.value w.normalized) (Finset.univ :Finset s)
    (fun i=>(T i).value) (fun i=>(T i).ramification)
    (fun i _=>(T i).normalized) (fun i _=>(T i).positive)
    (fun i _=>vertical_base A w (T i)) hsep b hb hbI
  have hdegree :B.natDegree≤j3 v A.polarPoly := calc
    B.natDegree = ∑ i:s,B.rootMultiplicity (i:L) := by
      rw [sum_coe_sort s (fun x :L=>B.rootMultiplicity x),(IsAlgClosed.splits B).natDegree_eq_card_roots,
        ← Multiset.toFinset_sum_count_eq B.roots]
      simp only [count_roots,s]
    _ ≤ ∑ i:s,KB (T i).value b:=sum_le_sum fun i _ =>
      (hm i).trans (order_le_normalization _ ha (hunit i c hc))
    _≤_:=hsum.trans_eq hn
  exact (Nat.mul_le_mul_left k hdegree).trans
    (base_coeff w hR hI (LinearMap.charpoly_monic _).ne_zero hD)
end
end qXARP7c
end
section
set_option autoImplicit true
namespace qWsLKEa
theorem proof :q0mTRkc.c7:=qXARP7c.proof
end qWsLKEa
end
end
