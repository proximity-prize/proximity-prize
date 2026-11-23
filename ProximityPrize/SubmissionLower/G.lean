import ProximityPrize.SubmissionLower.CC
import ProximityPrize.SubmissionLower.Z3EWiUc
import ProximityPrize.SubmissionLower.ZFFuWqa
import ProximityPrize.SubmissionLower.ZGlW6Oc
import ProximityPrize.SubmissionLower.ZgdIx1d
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.FiniteType → zUK, Algebra.IsAlgebraic → zjH, Algebra.IsIntegral → zVK, Algebra.smul_def → zd5, Algebra.trdeg → zls, CommRing → za6, DFunLike.congr_fun → zmU, Field → zrb, Fin.castLE → zQY, Finset → zJe, Finset.card_image_of_injective → ze7, Finset.exists_mem_eq_sup → zOU, Finset.subset_univ → ziq, Finset.sum_congr → zUp, Finset.sum_eq_single → zi6, Finset.sum_filter → zLJ, Finsupp.single → zhf, Finsupp.sum_of_support_subset → zWf, Function.Injective → zq4, Function.Injective.of_comp → z6j, Function.Surjective → zpX, Function.comp_apply → z3s, Ideal → znc, Ideal.IsIntegral.under_lt_under → zu8, Ideal.IsPrime.exists_mem_prime_of_ne_bot → zUo, Ideal.IsPrime.ne_top → zns, Ideal.Quotient.commRing → z0w, Ideal.Quotient.isDomain → zO0, Ideal.Quotient.lift → zP2, Ideal.Quotient.lift_mk → z0R, Ideal.Quotient.liftₐ → zTA, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_algebraMap → zOY, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.comap_comap → zg6, Ideal.comap_map_of_surjective → zEk, Ideal.eq_span_singleton_of_height_eq_one → zRh, Ideal.exists_ltSeries_of_hasGoingUp → z1m, Ideal.height_add_one_le_of_lt_of_isPrime → zSK, Ideal.height_le_ringKrullDim_of_isPrime → ztp, Ideal.map_comap_of_surjective → zNE, Ideal.map_le_iff_le_comap → zo0, Ideal.map_map → z0L, Ideal.map_span → zlN, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J
open _root_ renaming Ideal.mk_ker → zlC, Ideal.quotientEquivAlgOfEq → z9k, Ideal.quotientKerAlgEquivOfSurjective → zEK, Ideal.quotientMap → z3G, Ideal.quotientMap_injective → zmq, Ideal.quotientMap_mk → z5h, Ideal.span → zye, Ideal.span_singleton_generator → zOZ, Ideal.span_singleton_le_iff_mem → zvl, Ideal.subset_span → zCn, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsFractionRing.lift → zIj, IsFractionRing.lift_algebraMap → zoc, IsLocalization → zNo, IsLocalization.integerNormalization → zdR, IsLocalization.integerNormalization_spec → zXY, IsLocalization.isAlgebraic → zyQ, IsLocalization.map_under → zvH, IsLocalization.surj → zg4, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, LinearIndependent → z14, LinearMap.finrank_le_finrank_of_injective → zdv, Matrix.cons_val_one → z87, Matrix.cons_val_zero → zbs, Module.Finite → zAa, Module.finrank → zsE, Module.nontrivial_of_finrank_pos → zcE, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.X_pow_eq_monomial → zp9, MvPolynomial.algebraMap_def → zu9, MvPolynomial.algebraMap_eq → zKm, MvPolynomial.algebraMvPolynomial → z5R, MvPolynomial.coeff_C_mul → z06, MvPolynomial.coeff_monomial → z0I, MvPolynomial.coeff_sum → zqN, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.eval_X → zV6, MvPolynomial.eval_rename → zCp, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD
open _root_ renaming MvPolynomial.finSuccEquiv → z8s, MvPolynomial.finSuccEquiv_X_succ → z07, MvPolynomial.finSuccEquiv_X_zero → zOO, MvPolynomial.finSuccEquiv_apply → zyf, MvPolynomial.le_totalDegree → zY3, MvPolynomial.map → zDK, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.map_injective → zNV, MvPolynomial.monomial → ztt, MvPolynomial.monomial_fin_two → zXU, MvPolynomial.optionEquivLeft → zpj, MvPolynomial.optionEquivRight → zyD, MvPolynomial.rename → zHw, MvPolynomial.renameEquiv → zGY, MvPolynomial.renameEquiv_apply → zyl, MvPolynomial.rename_C → zt1, MvPolynomial.rename_X → z6l, MvPolynomial.ringHom_ext → zXT, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite → zmx, MvPolynomial.support_map_of_injective → zra, MvPolynomial.totalDegree → zph, MvPolynomial.totalDegree_le_of_dvd_of_isDomain → zCO, MvPolynomial.trdeg_of_isDomain → zUx, MvPolynomial.uniqueAlgEquiv_apply → zJG, MvPolynomial.uniqueFactorizationMonoid → zhK, Nat.card_eq_fintype_card → zey, Nat.eq_zero_of_le_zero → za7, Polynomial → zM1, Polynomial.C → z1z, Polynomial.C_injective → zmy, Polynomial.X → z7y, Polynomial.algebra → z88, Polynomial.algebraMap_eq → zrE, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.coe_mapRingHom → zKC, Polynomial.coeff_zero → zO6, Polynomial.commRing → zqU, Polynomial.evalRingHom → zhy, Polynomial.eval_C → zFf, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_C → zJU, Polynomial.instEuclideanDomain → zaz, Polynomial.isLocalization → zyz, Polynomial.ker_mapRingHom → zfT, Polynomial.mapRingHom → zhd, Polynomial.mapRingHom_comp → zPl, Polynomial.map_C → zrL
open _root_ renaming Polynomial.map_injective → zTo, Polynomial.map_surjective → zMr, Polynomial.natDegree_map_eq_of_injective → zt8, Polynomial.ringHom_ext → z86, Polynomial.trdeg_of_isDomain → zBA, RingHom.comap_ker → zEW, RingHom.comp_apply → zQb, RingHom.comp_assoc → zxS, RingHom.congr_fun → zLs, RingHom.injective → zyB, RingHom.injective_iff_ker_eq_bot → zli, RingHom.ker → zdq, RingHom.ker_comp_of_injective → zGm, RingHom.ker_eq_comap_bot → zPx, RingHom.ker_isPrime → zgL, RingHom.ker_ne_top → zZK, RingHom.toAlgebra → z9T, Set.image_singleton → zyk, Submodule.IsPrincipal.generator → z1N, Submonoid → zdT
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace YY
noncomputable section
open K1 cu gT MvPolynomial
open scoped Polynomial
open scoped BigOperators
private theorem bDf (a :L) :
  U7 a=algebraMap L FX a := by
 rw [zG3 L L[X] FX]
 rfl
theorem bnQ (Q:z3y (Fin 2) L) :
  (zDK U7 Q).totalDegree= Q.totalDegree := by
 unfold totalDegree
 rw [support_map_of_injective Q (fun a b hab=>(algebraMap L FX).injective
  (by simpa only [bDf] using hab))]
private theorem dO5 (C:aZ) (hC:C≠0) :
    ∃ Q:z3y (Fin 2) L,Q≠0∧Q.totalDegree≤C.totalDegree ∧
      ∀ x :Fin 2→L,zY9 (U7 ∘ x) C=0 →
        zY9 x Q=0:= by
  classical
  let b:=Module.Free.chooseBasis L FX
  obtain ⟨e,he⟩:=support_nonempty.mpr hC
  have he' : C.coeff e≠0:=mem_support_iff.mp he
  have hrepr :b.repr (C.coeff e)≠0:= fun hz=>he' (b.repr.injective
    (hz.trans (map_zero b.repr).symm))
  obtain ⟨j,hj⟩:=Finsupp.support_nonempty_iff.mpr hrepr
  let ℓ:=b.coord j
  have hℓ:ℓ (C.coeff e)≠0:=Finsupp.mem_support_iff.mp hj
  let Q:z3y (Fin 2) L := ∑ m∈C.support,monomial m (ℓ (C.coeff m))
  have hcoeff (m:Fin 2 →₀ ℕ) :Q.coeff m=ℓ (C.coeff m) := by
    by_cases hm:m∈C.support
    · rw [show Q = ∑ n∈C.support,monomial n (ℓ (C.coeff n)) from rfl,coeff_sum,
        Finset.sum_eq_single_of_mem m hm]
      · simp
      · intro n _ hnm
        simp [coeff_monomial,hnm]
    · rw [notMem_support_iff.mp hm,map_zero]
      change (∑ n∈C.support,monomial n (ℓ (C.coeff n))).coeff m=0
      rw [coeff_sum]
      apply Finset.sum_eq_zero
      intro n hn
      have hnm:n≠m:= fun h=>hm (h ▸ hn)
      simp [coeff_monomial,hnm]
  refine ⟨Q,fun hz=>hℓ (by simpa [hz] using (hcoeff e).symm),?_,?_⟩
  · apply Finset.sup_le
    intro m hm
    apply Finset.le_sup (f := fun m:Fin 2 →₀ ℕ=>m.degree)
    apply mem_support_iff.mpr
    intro hz
    exact (mem_support_iff.mp hm) (by rw [hcoeff,hz,map_zero])
  · intro x hx
    have hx' : zY9 (U7 ∘ x) C =
        ∑ m∈C.support,C.coeff m*U7 (m.prod fun i k=>x i^k) := by
      conv_lhs=>rw [C.as_sum]
      simp only [map_sum,eval_monomial,Finsupp.prod,map_prod,map_pow,z3s]
    have heval :zY9 x Q=ℓ (zY9 (U7 ∘ x) C) := by
      simp only [Q,hx',map_sum]
      refine zUp rfl fun m _ => ?_
      rw [eval_monomial,bDf,mul_comm (C.coeff m),← zd5,
        map_smul,smul_eq_mul,mul_comm]
    rw [heval,hx,map_zero]
private theorem eLU {k :Type} [zrb k]
   (A B:z3y (Fin 2) k) (hA:Irreducible A)
   (hB:B∉zye {A}) (S:zJe (Fin 2→k))
   (hzero : ∀ x∈S,zY9 x A=0∧zY9 x B=0) :
   S.card≤A.totalDegree*B.totalDegree := by
 let P:znc (z3y (Fin 2) k) :=zye {A}
 let J:=P ⊔ zye {B}
 have :UniqueFactorizationMonoid k :=PrincipalIdealRing.to_uniqueFactorizationMonoid
 have :UniqueFactorizationMonoid (z3y (Fin 2) k) :=
   zhK (Fin 2)
 have hprime :Prime A:=UniqueFactorizationMonoid.irreducible_iff_prime.mp hA
 have hp:P.IsPrime :=(Ideal.span_singleton_prime hA.ne_zero).mpr hprime
 have hdim: (affineHilbertPolynomial P).natDegree=1 := by
   have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one hA.ne_zero hp.ne_top
   change (affineHilbertPolynomial P).natDegree+1=Nat.card (Fin 2) at h
   simpa [zey] using h
 have hcut:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
   hp hB (b:=B.totalDegree) le_rfl
 have hjdim: (affineHilbertPolynomial J).natDegree=0 :=
   za7 (by simpa only [hdim,Nat.sub_self] using hcut.1)
 have hlead: (affineHilbertPolynomial P).leadingCoeff=(A.totalDegree :ℚ) := by
   have h:=affineDegree_span_singleton hA.ne_zero
   change affineDegree P= _ at h
   simpa [affineDegree,hdim] using h
 have hcoeff : (affineHilbertPolynomial J).coeff 0≤(B.totalDegree :ℚ)*(A.totalDegree :ℚ) := by
   simpa only [hdim,Nat.sub_self,Nat.cast_one,mul_one,hlead] using hcut.2
 have hsub: (S:Set (Fin 2→k))⊆zeroLocus k J:= by
   intro x hx
   apply mem_zeroLocus_iff_le_ker_aeval.mpr
   exact sup_le ((zvl _).mpr (RingHom.mem_ker.mpr (hzero x hx).1))
     ((zvl _).mpr (RingHom.mem_ker.mpr (hzero x hx).2))
 have hf :=finite_zeroLocus_and_ncard_le_affineDegree (K:=k) J hjdim
 have hs :=Set.ncard_le_ncard hsub hf.1
 rw [Set.ncard_coe_finset] at hs
 have hs' : (S.card:ℚ)≤((zeroLocus k J).ncard:ℚ) := by exact_mod_cast hs
 have hout:=hs'.trans (hf.2.trans ((affineDegree_of_natDegree_eq_zero hjdim).le.trans hcoeff))
 rw [mul_comm] at hout
 exact_mod_cast hout
theorem b9u (C:aZ) (hC:Irreducible C)
    (hmoving : ¬ by9 (zye {C})) (marks :zJe (Fin 2→L))
    (hmarks : ∀ x∈marks,zY9 (U7 ∘ x) C=0) :
    marks.card≤C.totalDegree^2 := by
  classical
  obtain ⟨Q,hQ,hdeg,hprotect⟩:=dO5 C hC.ne_zero
  let B:=zDK U7 Q
  have hBno:B≠0:= by
    intro hz
    apply hQ
    have hinj:zq4 (zDK (σ:=Fin 2) U7) :=
      zNV _ (fun a b h=>(algebraMap L FX).injective
        (by simpa only [bDf] using h))
    exact hinj (by simpa [B] using hz)
  have hBdeg:B.totalDegree≤C.totalDegree :=(bnQ Q).trans_le hdeg
  have hB:B∉(zye {C} : znc aZ) := by
    intro hin
    obtain ⟨r,hr⟩:=Ideal.mem_span_singleton.mp hin
    have hrne :r≠0:= fun hz=>hBno (by simp [hr,hz])
    have hdeg' : r.totalDegree=0:= by
      rw [hr,totalDegree_mul_of_isDomain hC.ne_zero hrne] at hBdeg
      omega
    have hunit :IsUnit r := by
      rw [totalDegree_eq_zero_iff_eq_C.mp hdeg']
      refine (isUnit_iff_ne_zero.mpr ?_).map znf
      intro hz
      exact hrne (by rw [totalDegree_eq_zero_iff_eq_C.mp hdeg',hz,map_zero])
    have hAssoc:Associated C B:= by
      obtain ⟨v,hv⟩:=hunit
      exact ⟨v,by simpa only [hv] using hr.symm⟩
    have hirrB:Irreducible B:=hAssoc.irreducible hC
    have hirrQ:Irreducible Q:= by
      refine ⟨fun h=>hirrB.not_isUnit (h.map (zDK U7)),?_⟩
      intro u v huv
      have hcases :=hirrB.isUnit_or_isUnit (show B=zDK U7 u *
          zDK U7 v by simp [B,huv])
      refine hcases.imp (fun hu => ?_) (fun hv => ?_)
      · rw [isUnit_iff_totalDegree_of_isReduced] at hu
        rw [bnQ] at hu
        rw [totalDegree_eq_zero_iff_eq_C.mp hu.2]
        refine (isUnit_iff_ne_zero.mpr fun hz=>hu.1.ne_zero ?_).map znf
        simp [coeff_map,hz]
      · rw [isUnit_iff_totalDegree_of_isReduced] at hv
        rw [bnQ] at hv
        rw [totalDegree_eq_zero_iff_eq_C.mp hv.2]
        refine (isUnit_iff_ne_zero.mpr fun hz=>hv.1.ne_zero ?_).map znf
        simp [coeff_map,hz]
    exact hmoving ⟨Q,hirrQ,Ideal.span_singleton_eq_span_singleton.mpr hAssoc⟩
  let embed (x :Fin 2→L) :Fin 2→FX:=U7 ∘ x
  have hinj:zq4 embed:= by
    intro a b hab
    funext i
    apply (algebraMap L FX).injective
    simpa only [embed,z3s,bDf] using congrFun hab i
  have hcount:=eLU C B hC hB (marks.image embed) (by
    intro v hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    refine ⟨hmarks x hx,?_⟩
    have hzQ:=hprotect x (hmarks x hx)
    change zY9 (U7 ∘ x) (zDK U7 Q)=0
    rw [eval_map,← eval₂_comp,hzQ,map_zero])
  rw [ze7 _ hinj] at hcount
  exact hcount.trans (by rw [pow_two]; exact Nat.mul_le_mul_left _ hBdeg)
end
end YY
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace YY
noncomputable section
open K1 cu gT
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ I:znc Ambient,bAG I →
    ∃ C:aZ,Irreducible C∧xg I=zye {C} ∧
      0<C.totalDegree∧C.totalDegree≤aef I
def c2 :Prop :=
  ∀ (I:znc Ambient) (C:z3y (Fin 2) L),bAG I →
    zAa aQ (as2 I)→ Irreducible C →
    xg I=zye {zDK U7 C} →
    ∃ g:ℕ,0<g∧bbt (Si I) g (a9E I) ∧
      C.totalDegree*g≤aef I
private theorem d2M (a b y v :FX) (q:kM) :
  zY9 ![a,b,y,v] (oi q)=zY9 ![a,b,y] q:= by
 change zY9 ![a,b,y,v] (zHw (zQY (by decide :3≤4)) q)= _
 rw [zCp]
 have hv : ![a,b,y,v] ∘ Fin.castLE (by decide :3≤4) = ![a,b,y] := by
  funext i
  fin_cases i <;> rfl
 rw [hv]
private theorem d2Q (a b y :FX) (C:aZ) :
  zY9 ![a,b,y] (pZ C)=zY9 ![a,b] C:= by
 change zY9 ![a,b,y] (zHw (zQY (by decide :2≤3)) C)= _
 rw [zCp]
 have hv : ![a,b,y] ∘ Fin.castLE (by decide :2≤3) = ![a,b] := by
  funext i
  fin_cases i <;> rfl
 rw [hv]
private theorem cag {I:znc Ambient} {z :K} {S:zM1 K}
  (h:IZ I z S) :aSf (Si I) z S:= by
 intro q hq
 have heval :aci z S (oi q)=aEE z S q :=
  d2M (jz z) (jz z^p) (kr S) (kr S.derivative) q
 exact RingHom.mem_ker.mpr (heval.symm.trans (RingHom.mem_ker.mp (h hq)))
private theorem c2p {I:znc Ambient} {z :K} {S:zM1 K}
  (h:IZ I z S) {C:aZ} (hC:C∈xg I) :qD z C=0:= by
 have heval :aEE z S (pZ C)=qD z C :=
  d2Q (jz z) (jz z^p) (kr S) C
 exact heval.symm.trans (RingHom.mem_ker.mp (cag h hC))
private theorem c0U (n:ℕ) (C:aZ) (hC:Irreducible C)
   (hmoving : ¬ by9 (zye {C})) (CF:zJe K)
   (hlabels : ∀ z∈CF,zY9 ![jz z,(jz z)^n] C=0) :
   CF.card≤C.totalDegree^2 := by
 let point (z :K) :Fin 2→L := ![algebraMap K L z,(algebraMap K L z)^n]
 have hinj:zq4 point := by
   intro a b hab
   exact (algebraMap K L).injective (congrFun hab 0)
 have hgraph (z :K) :U7 ∘ point z =
     ![jz z,(jz z)^n] := by
   funext i
   fin_cases i
   · rfl
   · change U7 ((algebraMap K L z)^n)=(jz z)^n
     exact map_pow U7 _ n
 have hc:=b9u C hC hmoving (CF.image point) (by
   intro x hx
   obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hx
   rw [hgraph]
   exact hlabels z hz)
 simpa only [ze7 _ hinj] using hc
private theorem ddj (C:aZ) (hC:C≠0) (hdeg:C.totalDegree<p)
  (CF:zJe K) (hlabels : ∀ z∈CF,qD z C=0) :
  CF.card≤(p+1)*C.totalDegree := by
 classical
 have hc:=bqt p C.totalDegree C.totalDegree (by decide)
  C hC (C.degreeOf_le_totalDegree 0) hdeg (C.degreeOf_le_totalDegree 1)
  (CF.image jz) (by
    intro a ha
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp ha
    exact hlabels z hz)
 simpa only [ze7 _ jz.injective,Nat.add_mul,Nat.one_mul,
  Nat.add_comm C.totalDegree] using hc
private theorem b1I (C:aZ) (hC:C≠0) (Q:z3y (Fin 2) L)
  (h:zye {C} = zye {zDK U7 Q}) :
  C.totalDegree= Q.totalDegree := by
 have ha :=Ideal.span_singleton_eq_span_singleton.mp h
 have hQ:zDK U7 Q≠0:= by
  obtain ⟨v,hv⟩:=ha
  exact fun hz=>mul_ne_zero hC (Units.ne_zero v) (hv.trans hz)
 rw [← bnQ Q]
 exact (zCO ha.dvd_dvd.1 hQ).antisymm
  (zCO ha.dvd_dvd.2 hC)
private theorem diE {ι:Type*} (s :zJe ι) (W:ι→zJe K) :
  ((s.biUnion W).card:ℚ) ≤ ∑ i∈s,((W i).card:ℚ) := by
 exact_mod_cast (Finset.card_biUnion_le (s :=s) (t:=W))
end
end YY
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GK
noncomputable section
open K1 cu gT YY Polynomial
open scoped Polynomial BigOperators
def Fp {R:Type} [za6 R] (s t:R) :Fin 2→R[X] :=
 ![z1z t - z1z s*(z7y:R[X]),z7y]
def FT:z3y (Fin 2) aQ →ₐ[aQ] aQ[X] :=
 MvPolynomial.aeval (Fp (ek 0) (ek 1))
def ajM:aZ →+* aQ[X] :=
 FT.toRingHom.comp (zDK (algebraMap FX aQ))
private theorem bp9 (e :Fin 2 →₀ ℕ) :e.sum (fun _ m=>m)=e 0+e 1 := by
 simp [zWf e (ziq e.support)]
private def J0:aZ →+* aZ[X] :=
 zOD (Polynomial.C.comp (znf:FX →+* aZ))
  (Fp (z9v 0) (z9v 1))
private theorem bLv :
   (mapRingHom (algebraMap aZ aQ)).comp J0=ajM:= by
 apply zXT
 · intro a
   simp [J0,ajM,FT,zrE,zQb]
   rfl
 · intro k
   fin_cases k <;>
     simp [J0,ajM,FT,Fp,zQb,ek]
private theorem bIv {R:Type} [za6 R] (s t:R) :
  (Fp s t 0).natDegree≤1 := by
 change (z1z t - z1z s*(z7y:R[X])).natDegree≤1
 have hs : (z1z s*(z7y:R[X])).natDegree≤1 := by
  simpa only [pow_one] using natDegree_C_mul_X_pow_le s 1
 exact (natDegree_sub_le _ _).trans (max_le (by simp) hs)
private theorem bXM (e :Fin 2 →₀ ℕ) (a :FX) (d:ℕ)
   (he :e 0+e 1≤d) :
   (J0 (ztt e a)).coeff d =
     if e 0+e 1=d then znf a*(-MvPolynomial.X 0)^e 0 else 0:= by
 let q:aZ[X] :=Fp (z9v 0) (z9v 1) 0
 have hq:q.natDegree≤1 :=bIv _ _
 have hcoeff :q.coeff 1 = -(z9v 0:aZ) := by simp [q,Fp,coeff_sub]
 have hpow: (q^e 0).natDegree≤e 0:= by simpa using natDegree_pow_le_of_le (e 0) hq
 have hXpow: ((z7y:aZ[X])^e 1).natDegree≤e 1 := by simp
 have hqpow: (q^e 0).coeff (e 0)=(-(z9v 0:aZ))^e 0:= by
   simpa [hcoeff] using (coeff_pow_of_natDegree_le (m:=e 0) hq)
 rw [zXU,map_mul,map_mul,map_pow,map_pow]
 simp only [J0,Fp,zTv,zrD,
   zQb,zbs,z87]
 change ((z1z (znf a)*q^e 0)*z7y ^e 1).coeff d= _
 rw [mul_assoc,coeff_C_mul]
 split_ifs with heq
 · rw [← heq,coeff_mul_add_eq_of_natDegree_le hpow hXpow,hqpow,coeff_X_pow_self]
   simp
 · rw [coeff_eq_zero_of_natDegree_lt,mul_zero]
   exact (natDegree_mul_le_of_le hpow hXpow).trans_lt (lt_of_le_of_ne he heq)
theorem bO8 (F:aZ) : (ajM F).natDegree=F.totalDegree := by
  classical
  have hu: (ajM F).natDegree≤F.totalDegree := by
    change (FT (zDK (algebraMap FX aQ) F)).natDegree≤F.totalDegree
    have hvar (i:Fin 2) : (Fp (ek 0) (ek 1) i).natDegree≤1 := by
      fin_cases i
      · exact bIv _ _
      · simp [Fp]
    have h:=MvPolynomial.natDegree_aeval_le_weightedTotalDegree_of_le (1 :Fin 2→ℕ)
      _ (zDK (algebraMap FX aQ) F) hvar
    simpa [FT,MvPolynomial.weightedTotalDegree_one,
      zra _ (zyB (algebraMap FX aQ)),zph]
      using h
  refine hu.antisymm ?_
  by_cases hF:F=0
  · simp [hF]
  let d:=F.totalDegree
  obtain ⟨e,he,hde⟩:=zOU F.support
    (MvPolynomial.support_nonempty.mpr hF) (fun e=>e.sum (fun _ m=>m))
  change d=e.sum (fun _ m=>m) at hde
  rw [bp9] at hde
  have htop: (J0 F).coeff d≠0:= by
    have hh (e' : Fin 2 →₀ ℕ) (he' : e' ∈ F.support) :e' 0+e' 1≤d:= by
      rw [← bp9]
      exact zY3 he'
    have hexp :
        (J0 F).coeff d =
          ∑ e' ∈ F.support with e' 0+e' 1=d,
            znf (F.coeff e')*(-MvPolynomial.X 0)^e' 0:= by
      conv_lhs=>rw [F.as_sum]
      rw [map_sum,finsetSum_coeff,zLJ]
      exact zUp rfl (fun e' he' =>
        bXM e' (F.coeff e') d (hh e' he'))
    have hcoef (a :FX) (k m:ℕ) :
        (znf a*(-(z9v 0:aZ))^k).coeff (zhf 0 m)
          = if k=m then a*(-1)^k else 0:= by
      have hneg: (znf (-1 :FX) :aZ) = -1 :=
        (map_neg (znf:FX →+* aZ) 1).trans
          (congrArg Neg.neg (map_one (znf:FX →+* aZ)))
      have hn : -(z9v 0:aZ)=znf (-1 :FX)*z9v 0 :=
        (neg_one_mul (z9v 0:aZ)).symm.trans
          (congrArg (fun z=>z*(z9v 0:aZ)) hneg.symm)
      rw [hn,mul_pow,← map_pow,← mul_assoc,← map_mul,z06,
        zp9,z0I]
      by_cases hk :k=m
      · simp [hk]
      · have hs :zhf (0:Fin 2) k≠zhf 0 m:= by
          intro h
          exact hk (by simpa using zmU h 0)
        simp [hk,hs]
    intro ht
    have hz :=congrArg (fun f :aZ=>f.coeff (zhf 0 (e 0))) ht
    rw [hexp] at hz
    simp only [zqN,AddMonoidAlgebra.coeff_zero,hcoef] at hz
    rw [zi6 e] at hz
    · have hz' : F.coeff e*(-1 :FX)^e 0=0:= by simpa using hz
      exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp he)
        (pow_ne_zero (e 0) (neg_ne_zero.mpr one_ne_zero))) hz'
    · intro e' he' hne
      have hdiff :e' 0≠e 0:= by
        intro h0
        have h1 :e' 1=e 1 := by
          have :=(Finset.mem_filter.mp he').2
          omega
        exact hne (Finsupp.ext (by intro i; fin_cases i <;> assumption))
      simp [hdiff]
    · exact fun h=>False.elim (h (Finset.mem_filter.mpr ⟨he,hde.symm⟩))
  apply le_natDegree_of_ne_zero
  have hr :ajM F=(J0 F).map (algebraMap aZ aQ) :=
    (zLs bLv F).symm
  rw [hr,coeff_map]
  exact fun h=>htop (zxb aZ aQ (h.trans (map_zero _).symm))
end
end GK
end
section
namespace aRZ
noncomputable section
open cu gT pI
def aQa :aQ →+* dV :=
  let indices :Fin 2→Fin 4 := ![0,2]
  let rename :aZ →+* z3y (Fin 4) FX :=
    (zHw indices).toRingHom
  let g:aZ →+* dV :=
    (algebraMap (z3y (Fin 4) FX) dV).comp rename
  have hi:zq4 indices := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [indices]
  zIj (K:=aQ) (g:=g)
    ((zxb (z3y (Fin 4) FX) dV).comp
      (MvPolynomial.rename_injective indices hi))
def aOQ (f :aZ) :zM1 dV :=
 (GK.ajM f).map aQa
end
end aRZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 8
namespace aRZ
noncomputable section
open K1 cu gT pI YY
def c1 :Prop :=
  ∀ I:znc Ambient,I.IsPrime→ ringKrullDim (gk I)=2 →
    zAa dV (Ik I) →
    ∀ f :aZ,f≠0→xg I=zye {f} →
      ∃ e : (zM1 dV ⧸ zye {aOQ f}) →ₐ[dV]
          Ik I,zq4 e
def c2 :Prop :=
  ∀ I:znc Ambient,I.IsPrime→ ringKrullDim (gk I)=2 →
    (xg I).IsMaximal→zAa aQ (Lj I) →
    (∃ (z :K) (R:zM1 K),IZ I z R)→0<pN I 3
private abbrev AH :aZ →+* Ambient:=oi.comp pZ
private theorem bg7 (I:znc Ambient) [I.IsPrime] : (xg I).IsPrime :=
 (inferInstance :I.IsPrime).comap AH
private theorem d2S {k :Type} [za6 k] (a b y v :k)
    (f :z3y (Fin 2) k) :
    zY9 ![a,b,y,v]
      (MvPolynomial.rename (Fin.castLE (by decide :3≤4))
        (MvPolynomial.rename (Fin.castLE (by decide :2≤3)) f)) =
      zY9 ![a,b] f := by
  let cast34 :=zQY (by decide :3≤4)
  let cast23:=zQY (by decide :2≤3)
  rw [zCp,zCp]
  have he : (![a,b,y,v] ∘ cast34) ∘ cast23 = ![a,b] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
private theorem co7 {I:znc Ambient} {z :K} {R:zM1 K}
  (h:IZ I z R) :xg I≤zdq (qD z) := by
 intro f hf
 have hmem:AH f∈I:=hf
 have he :aci z R (AH f)=qD z f :=
  d2S (jz z) (jz z^p) (kr R) (kr R.derivative) f
 exact RingHom.mem_ker.mpr (he.symm.trans (RingHom.mem_ker.mp (h hmem)))
private abbrev X6 (I:znc Ambient) :=FractionRing (Ambient ⧸ I)
private def gxE (I:znc Ambient) :Ambient →+* X6 I:= by
 let q:Ambient →+* (Ambient ⧸ I) :=zVv I
 let ι: (Ambient ⧸ I) →+* X6 I:=algebraMap _ _
 exact ι.comp q
private theorem bND (I:znc Ambient) [I.IsPrime]
    [zAa aQ (Y0 I)] (hz :pN I 0=0) :
    xg I ≠ ⊥ := by
  intro hI
  let F:=X6 I
  let π:=gxE I
  have hker :zdq π=I:= by
    change zdq ((algebraMap (Ambient ⧸ I) (X6 I)).comp
      (zVv I))=I
    rw [zGm _ (zxb (Ambient ⧸ I) (X6 I)),
      zlC]
  have hseed :zq4 (π.comp AH) := by
    rw [zli,← zEW,hker]
    exact hI
  let ρ:aQ →+* F:=zIj hseed
  have hρ (f :aZ) :ρ (algebraMap aZ aQ f)=π (AH f) :=
    zoc hseed f
  let e :vR →+* F:=zOD ρ
    ![π (z9v 2),π (z9v 3)]
  have hcomp:e.comp Dk=π:= by
    apply zXT
    · intro a
      simp only [zQb,Dk,zTv,e]
      have hC:AH (znf a)=znf a := by
        change zHw _ (zHw _ (znf a))= _
        rw [zt1,zt1]
      rw [zG3 FX aZ aQ,zKm]
      exact (hρ _).trans (congrArg π hC)
    · intro i
      fin_cases i
      · simpa [zQb,e,Dk,ek,AH,pZ,oi]
          using hρ (z9v 0)
      · simpa [zQb,e,Dk,ek,AH,pZ,oi]
          using hρ (z9v 1)
      · simp [e,Dk]; rfl
      · simp [e,Dk]; rfl
  have hmap :I.map Dk≤zdq e := by
    rw [zo0,zEW,hcomp,hker]
  have htop:I.map Dk = ⊤ :=
    Ideal.Quotient.subsingleton_iff.mp
      ((Module.finrank_eq_zero_iff_of_free aQ (Y0 I)).mp hz)
  exact zZK e (top_unique (htop ▸ hmap))
private theorem goh (I:znc Ambient) [I.IsPrime]
   (hn:xg I ≠ ⊥) (hm : ¬ (xg I).IsMaximal) :
   ∃ f :aZ,f≠0∧xg I=zye {f} := by
 let P:=xg I
 let:P.IsPrime :=bg7 I
 have hlo:1≤P.height:= by
   simpa using zSK (bot_lt_iff_ne_bot.mpr hn)
 obtain ⟨M,hM,hPM⟩:=P.exists_le_maximal (zns ‹P.IsPrime›)
 let:M.IsPrime :=hM.isPrime
 have hlt:P<M:=lt_of_le_of_ne hPM fun h=> by
   have he :xg I=M:=h
   exact hm (he.symm ▸ hM)
 have hdim:ringKrullDim aZ=2 := by
   rw [zmx,ringKrullDim_eq_zero_of_field]
   norm_num [zey]
 have hMheight:M.height≤2 := by
   have h:=ztp (I:=M)
   rw [hdim] at h
   exact WithBot.coe_le_coe.mp h
 have hle :P.height≤1 :=
   (ENat.add_le_add_iff_right (by simp : (1 :ℕ∞) ≠ ⊤)).mp
     ((Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hMheight)
 have :UniqueFactorizationMonoid FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
 have :UniqueFactorizationMonoid aZ:=zhK (Fin 2)
 obtain ⟨f,hmem,hf⟩:=zUo (bg7 I) hn
 exact ⟨f,hf.ne_zero,zRh (hle.antisymm hlo) hmem hf⟩
private theorem glx {I:znc Ambient} (hI: (xg I).IsMaximal)
  {z w:K} {R S:zM1 K} (hz :IZ I z R) (hw:IZ I w S) :
  (jz z,jz z^p)=(jz w,jz w^p) := by
 have hker :=hI.eq_of_le (zZK (qD z)) (co7 hz)
 have hx : (z9v 0-MvPolynomial.C (jz z) :aZ)∈xg I:= by
  rw [hker]
  apply RingHom.mem_ker.mpr
  simp [qD]
 have he :=RingHom.mem_ker.mp (co7 hw hx)
 have he' : jz w=jz z := by
  simpa [qD,sub_eq_zero] using he
 rw [he']
theorem of_children (h1 :c1) (h2 :c2) :YX.c6:= by
  classical
  intro I hI hdim hfinite hz
  let:I.IsPrime :=hI
  let:zAa aQ (Y0 I) :=hfinite.Kw
  let:zAa dV (Ik I) :=hfinite.kK
  by_cases hm: (xg I).IsMaximal
  · by_cases hmark : ∃ (z :K) (R:zM1 K),IZ I z R
    · obtain ⟨z,R,hon⟩:=hmark
      refine ⟨⟨1,one_ne_zero,{(jz z,jz z^p)}⟩,by simp,
        ?_,?_⟩
      · simp only [Finset.card_singleton]
        exact Nat.succ_le_of_lt (h2 I hI hdim hm hfinite.Bo ⟨z,R,hon⟩)
      · intro w S hw
        exact Or.inr (Finset.mem_singleton.mpr (glx hm hw hon))
    · exact ⟨⟨1,one_ne_zero,∅⟩,by simp,by simp,fun w S hw=>(hmark ⟨w,S,hw⟩).elim⟩
  · obtain ⟨f,hf,hgen⟩:=goh I (bND I hz) hm
    obtain ⟨e,he⟩:=h1 I hI hdim hfinite.kK f hf hgen
    have hdegree : (aOQ f).natDegree=f.totalDegree := by
      rw [aOQ,zt8 aQa.injective,
        GK.bO8]
    have hbound:=zdv (f :=e.toLinearMap) he
    rw [finrank_quotient_span_eq_natDegree,hdegree] at hbound
    refine ⟨⟨f,hf,∅⟩,hbound,by simp,?_⟩
    intro z R hon
    have hmem:f∈xg I:= by
      rw [hgen]
      exact zCn (Set.mem_singleton f)
    exact Or.inl (RingHom.mem_ker.mp (co7 hon hmem))
end
end aRZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GK
noncomputable section
open K1 cu gT YY
open scoped Polynomial
abbrev Raw (n:ℕ) :=z3y (Fin n) FX
abbrev Over (n:ℕ) :=z3y (Fin n) aQ
local instance (n:ℕ) (I:znc (Raw n)) :za6 (gk I)[X] :=
 @zqU (gk I) (z0w I)
abbrev i9 {n:ℕ} (I:znc (Raw n)) (i j:Fin n) :znc (Over n) :=
 I.map (zDK (algebraMap FX aQ)) ⊔ zye {B4 i j}
abbrev Slice {n:ℕ} (I:znc (Raw n)) (i j:Fin n) :=Over n ⧸ i9 I i j
abbrev coord {n:ℕ} (I:znc (Raw n)) (k :Fin n) :gk I :=
 zVv I (z9v k)
def qw {n:ℕ} (I:znc (Raw n)) (i j:Fin n) :
    aZ →+* (gk I)[X] :=
  zOD (Polynomial.C.comp (algebraMap FX (gk I)))
    ![z7y,z1z (coord I i)+Polynomial.X*z1z (coord I j)]
def toSlice {n:ℕ} (I:znc (Raw n)) (i j:Fin n) :gk I →+* Slice I i j :=
  z3G (i9 I i j) (zDK (algebraMap FX aQ))
    (Ideal.map_le_iff_le_comap.mp le_sup_left)
def vV {n:ℕ} (I:znc (Raw n)) (i j:Fin n) :
    (gk I)[X] →+* Slice I i j :=
  zqf (toSlice I i j) (algebraMap aQ (Slice I i j) (ek 0))
theorem bNY {n:ℕ} (I:znc (Raw n)) (i j:Fin n) :
    toSlice I i j (coord I i) +
      algebraMap aQ (Slice I i j) (ek 0)*toSlice I i j (coord I j) =
      algebraMap aQ (Slice I i j) (ek 1) := by
  have h:zVv (i9 I i j) (B4 i j)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show zye {B4 i j} ≤ i9 I i j from le_sup_right)
        (z5J _))
  apply sub_eq_zero.mp
  simpa only [B4,map_sub,map_add,map_mul,← zKm,
    zOY,toSlice,coord,z5h,z7N] using h
theorem aEa {n:ℕ} (I:znc (Raw n)) (i j:Fin n) :
   (vV I i j).comp (qw I i j) =
     (algebraMap aQ (Slice I i j)).comp (algebraMap aZ aQ) := by
 apply zXT
 · intro a
   simp [qw,vV,zQb,toSlice,zKm]
   rfl
 · intro k
   fin_cases k
   · simp [qw,vV,zQb,ek]
   · have h:=bNY I i j
     rw [mul_comm (algebraMap aQ (Slice I i j) (ek 0)) (toSlice I i j (coord I j))] at h
     simpa [qw,vV,zQb,ek] using h
theorem bKi {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
  [Nontrivial (Slice I i j)] :zq4 (qw I i j) := by
 have h:=(zyB (algebraMap aQ (Slice I i j))).comp
  (zxb aZ aQ)
 have hf :zq4 ((vV I i j).comp (qw I i j)) := by
  rw [aEa]
  exact h
 exact z6j hf
private abbrev FunctionField {n:ℕ} (I:znc (Raw n)) :=
 FractionRing ((gk I)[X])
private def aM0 {n:ℕ} (I:znc (Raw n)) (i j:Fin n) [I.IsPrime]
  [Nontrivial (Slice I i j)] :aQ →+* FunctionField I :=
 zIj (K:=aQ)
  (g:=(algebraMap (gk I)[X] (FunctionField I)).comp (qw I i j))
  ((zxb (gk I)[X] (FunctionField I)).comp
    (bKi I i j))
private theorem bcE {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
  [I.IsPrime] [Nontrivial (Slice I i j)] (d:aZ) :
  aM0 I i j (algebraMap aZ aQ d) =
    algebraMap (gk I)[X] (FunctionField I) (qw I i j d) :=
 zoc _ d
private theorem cGA {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
  [I.IsPrime] [Nontrivial (Slice I i j)] (k :Fin 2) :
  aM0 I i j (ek k) =
    algebraMap (gk I)[X] (FunctionField I) (qw I i j (z9v k)) :=
 bcE I i j _
private def aWt {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
  [I.IsPrime] [Nontrivial (Slice I i j)] :Over n →+* FunctionField I :=
 zOD (aM0 I i j)
  (fun k=>algebraMap (gk I)[X] (FunctionField I) (z1z (coord I k)))
private theorem bti {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] :
    (aWt I i j).comp (zDK (algebraMap FX aQ)) =
      ((algebraMap (gk I)[X] (FunctionField I)).comp z1z).comp
        (zVv I) := by
  apply zXT
  · intro a
    simp only [zQb,zpw,aWt,zTv]
    have ha :algebraMap FX aQ a=algebraMap aZ aQ (znf a) :=rfl
    rw [ha,bcE]
    simp only [qw,zTv,zQb]
    rfl
  · intro k
    simp [aWt,zQb]
private theorem ezd {n:ℕ} {B:Type} [za6 B] (f :Over n →+* B)
    (i j:Fin n) :f (B4 i j) =
      f (z9v i)+f (znf (ek 0))*f (z9v j) -
        f (znf (ek 1)) := by
  simp only [B4,map_sub,map_add,map_mul]
private theorem eyT {A B:Type} [za6 A] [za6 B] (f :A →+* B)
  (a b s :A) :f a+f s*f b - f (a+s*b)=0:= by
 rw [f.map_add,f.map_mul,sub_self]
set_option maxHeartbeats 1500000 in
private def aE0 {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] :Slice I i j →+* FunctionField I :=
  zP2 (i9 I i j) (aWt I i j) <| by
    change i9 I i j≤zdq (aWt I i j)
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro x hx
      change ((aWt I i j).comp (zDK (algebraMap FX aQ))) x=0
      rw [bti]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    · intro x hx
      obtain rfl :=Set.mem_singleton_iff.mp hx
      apply RingHom.mem_ker.mpr
      let f :=aWt I i j
      let m: (gk I)[X] →+* FunctionField I :=
        algebraMap (gk I)[X] (FunctionField I)
      have hX (k :Fin n) :f (z9v k)=m (z1z (coord I k)) :=
        zrD (aM0 I i j)
          (fun k=>m (z1z (coord I k))) k
      have hC (k :Fin 2) :f (znf (ek k)) =
          m (qw I i j (z9v k)) :=
        (zTv (aM0 I i j)
          (fun k=>m (z1z (coord I k))) (ek k)).trans
            (cGA I i j k)
      have hs :qw I i j (z9v 0)=Polynomial.X:= by
        simp only [qw,zrD,zbs]
      have ht:qw I i j (z9v 1) =
          z1z (coord I i)+Polynomial.X*z1z (coord I j) := by
        simp only [qw,zrD,z87,zbs]
      have h:=ezd f i j
      rw [hX i,hX j,hC 0,hC 1,hs,ht] at h
      exact h.trans (eyT m _ _ _)
private theorem cpQ {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
   [I.IsPrime] [Nontrivial (Slice I i j)] :
   (aE0 I i j).comp (vV I i j) =
     algebraMap (gk I)[X] (FunctionField I) := by
 apply z86
 · intro a
   obtain ⟨a,rfl⟩:=zld a
   simpa [aE0,vV,toSlice,zQb] using
     zLs (bti I i j) a
 · simp only [zQb,vV,z4Q,Polynomial.eval₂_X]
   change aE0 I i j (zVv (i9 I i j) (znf (ek 0)))= _
   simp only [aE0,z0R,aWt,zTv,
     cGA,qw,zrD,zbs]
theorem aQr {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
  [I.IsPrime] [Nontrivial (Slice I i j)] :zq4 (vV I i j) := by
 have hf :zq4 ((aE0 I i j).comp (vV I i j)) := by
  rw [cpQ]
  exact zxb (gk I)[X] (FunctionField I)
 exact z6j hf
private theorem aG3 {n:ℕ} (I:znc (Raw n)) (i j:Fin n)
    (x :Slice I i j) :
    ∃ (q: (gk I)[X]) (d:aZ),d≠0 ∧
      x*algebraMap aQ (Slice I i j) (algebraMap aZ aQ d) =
        vV I i j q:= by
  let:zZE (z3y (Fin n) aZ) (Over n) :=z5R
  obtain ⟨f,rfl⟩:=zld x
  obtain ⟨⟨g,m⟩,hgm⟩:=zg4
    (M:=(nonZeroDivisors aZ).map (znf (σ:=Fin n))) f
  obtain ⟨d,hd,hdm⟩:=m.property
  let lift:z3y (Fin n) aZ →+* (gk I)[X] :=
    zOD (qw I i j) (fun k=>z1z (coord I k))
  have hcomp: (vV I i j).comp lift =
      (zVv (i9 I i j)).comp
        (zDK (algebraMap aZ aQ)) := by
    apply zXT
    · intro a
      simp only [zQb,lift,zTv,zpw]
      rw [← zKm,zOY]
      exact zLs (aEa I i j) a
    · intro k
      simp [lift,vV,toSlice,zQb]
  refine ⟨lift g,d,mem_nonZeroDivisors_iff_ne_zero.mp hd,?_⟩
  have hgm' : f*znf (algebraMap aZ aQ d) =
      zDK (algebraMap aZ aQ) g:= by
    simpa only [zu9,← hdm,zpw] using hgm
  calc
    _=zVv (i9 I i j) (f*znf (algebraMap aZ aQ d)) :=
      (map_mul _ _ _).symm
    _ = _:=(congrArg (zVv (i9 I i j)) hgm').trans
      (zLs hcomp g).symm
abbrev SG (P:znc aZ) :=Slice P 0 1
private abbrev AH :=oi.comp pZ
private abbrev a8q:Over 2 →ₐ[aQ] Over 4 :=
 zHw (zQY (by decide :2≤4))
theorem bg7 (I:znc Ambient) [I.IsPrime] : (xg I).IsPrime :=
 (inferInstance :I.IsPrime).comap AH
private def aii (I:znc Ambient) :gk (xg I) →+* gk I :=
 z3G I AH le_rfl
private theorem goA (I:znc Ambient) :zq4 (aii I) :=
 zmq
theorem eLY (I:znc Ambient) [Nontrivial (rM I)] :
    zq4 (qw (xg I) 0 1) := by
  have h: (zhd (aii I)).comp (qw (xg I) 0 1) =
      qw I 0 1 := by
    apply zXT
    · intro a
      simp only [zQb,qw,zTv,
        zKC,zrL,aii]
      change z1z ((zVv I)
        (AH (znf a)))=z1z (algebraMap FX (gk I) a)
      rw [show AH (znf a)=znf a by simp [oi,pZ]]
      rfl
    · intro k
      fin_cases k
      · simp [qw]
      · simp [qw,aii,oi,pZ,coord,zQb]
  have hinj:zq4 ((zhd (aii I)).comp
      (qw (xg I) 0 1)) := by
    rw [h]
    exact bKi I 0 1
  exact z6j hinj
private theorem dcN :
   (a8q.toRingHom).comp (zDK (algebraMap FX aQ)) =
     (zDK (algebraMap FX aQ)).comp AH := by
 apply zXT
 · intro a
   simp [oi,pZ,zQb]
 · intro k
   simp [oi,pZ,zQb]
private theorem gok :a8q (B4 0 1)=B4 0 1 := by
 simp [B4]
private theorem eLV (I:znc Ambient) :
   i9 (xg I) 0 1≤(i9 I 0 1).comap a8q:= by
 refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
 · intro p hp
   change (a8q.toRingHom.comp (zDK (algebraMap FX aQ))) p ∈
    i9 I 0 1
   rw [dcN]
   exact (show I.map (zDK (algebraMap FX aQ)) ≤
    i9 I 0 1 from le_sup_left) (z7X _ hp)
 · intro p hp
   obtain rfl :=Set.mem_singleton_iff.mp hp
   change a8q (B4 0 1)∈i9 I 0 1
   rw [gok]
   exact (show zye {B4 0 1} ≤ i9 I 0 1 from le_sup_right)
    (z5J _)
def aWo (I:znc Ambient) :SG (xg I) →ₐ[aQ] rM I :=
 Ideal.quotientMapₐ (i9 I 0 1) a8q (eLV I)
private theorem eL0 (I:znc Ambient) :
    (aWo I).toRingHom.comp (vV (xg I) 0 1) =
      (vV I 0 1).comp (zhd (aii I)) := by
  apply z86
  · intro a
    obtain ⟨a,rfl⟩:=zld a
    change aWo I (vV (xg I) 0 1
        (z1z (zVv (xg I) a))) =
      vV I 0 1 (Polynomial.map (aii I)
        (z1z (zVv (xg I) a)))
    simp only [vV,z4Q,zJU,
      zrL,toSlice,aii,z5h,
      aWo,Ideal.quotient_map_mkₐ,Ideal.Quotient.mkₐ_eq_mk]
    have h:=zLs dcN a
    change a8q (zDK (algebraMap FX aQ) a) =
      zDK (algebraMap FX aQ) (AH a) at h
    exact congrArg (zVv (i9 I 0 1)) h
  · simp [vV,zQb]
theorem c4d (I:znc Ambient) [I.IsPrime] [Nontrivial (rM I)] :
  zq4 (aWo I) := by
 apply (injective_iff_map_eq_zero (aWo I)).mpr
 intro x hx
 obtain ⟨q,d,hd,hq⟩:=aG3 (xg I) 0 1 x
 have hq' := congrArg (aWo I) hq
 rw [map_mul,hx,zero_mul] at hq'
 have hzero :vV I 0 1 (Polynomial.map (aii I) q)=0:= by
  exact (zLs (eL0 I) q).symm.trans hq'.symm
 have hq0:q=0:=(Polynomial.map_eq_zero_iff (goA I)).mp
  ((injective_iff_map_eq_zero _).mp (aQr I 0 1) _ hzero)
 rw [hq0,map_zero] at hq
 have hd' : algebraMap aZ aQ d≠0 :=
  fun h=>hd (zxb aZ aQ (h.trans (map_zero _).symm))
 exact ((isUnit_iff_ne_zero.mpr hd').map (algebraMap aQ (SG (xg I)))).mul_right_cancel
  (hq.trans (zero_mul _).symm)
end
end GK
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
namespace aKw
noncomputable section
open cu gT YY Polynomial Algebra AlgebraicIndependent
open scoped Polynomial
abbrev zI (I:znc Ambient) :=gk I
abbrev Image (I:znc Ambient) :=gk (xg I)
abbrev coord (I:znc Ambient) (i:Fin 4) :zI I :=
 zVv I (z9v i)
abbrev AH :aZ →+* Ambient:=oi.comp pZ
def aDo (I:znc Ambient) :Image I →+* zI I :=
 z3G I AH le_rfl
theorem enF (I:znc Ambient) :
  zq4 (aDo I) :=
 zmq
private theorem cR2 (k R:Type) [zrb k] [za6 R] [ztn R]
   [zZE k R] [zUK k R] :
   ∃ n:ℕ,ringKrullDim R=n∧trdeg k R=n:= by
 obtain ⟨n,g,hg,hint⟩:=exists_integral_inj_algHom_of_fg k R
 let N :=z3y (Fin n) k
 letI:zZE N R:=g.toRingHom.toAlgebra
 letI:zsf k N R:=zsL fun a=>(g.commutes a).symm
 letI:FaithfulSMul N R:=(faithfulSMul_iff_algebraMap_injective N R).mpr hg
 letI:zVK N R:=⟨hint⟩
 let h:=PrimeSpectrum.comap (algebraMap N R)
 have hmono:StrictMono h:= by
   intro a b hab
   letI:a.asIdeal.IsPrime :=a.2
   exact zu8 (R:=N) hab
 have hsurj:zpX h:=Algebra.IsIntegral.comap_surjective N R
 have hdim:ringKrullDim R=ringKrullDim N := by
   refine (Order.krullDim_le_of_strictMono h hmono).antisymm ?_
   rw [Order.krullDim_eq_iSup_length,Order.krullDim_eq_iSup_length]
   apply WithBot.coe_le_coe.mpr
   apply iSup_le
   intro l
   obtain ⟨P,hP⟩:=hsurj l.head
   letI:P.asIdeal.IsPrime :=P.2
   letI:P.asIdeal.LiesOver l.head.asIdeal:=⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
   obtain ⟨L,hL,_,_⟩:=z1m l P.asIdeal
   exact hL ▸ le_iSup (fun L:LTSeries (PrimeSpectrum R)=>(L.length:ℕ∞)) L
 refine ⟨n,?_,?_⟩
 · rw [hdim,zmx,
     ringKrullDim_eq_zero_of_field,zero_add,zey,Fintype.card_fin]
 · have halg:zjH N R :=
     ⟨fun x=>(show IsIntegral N x from hint x).isAlgebraic⟩
   have hzero :trdeg N R=0 := @trdeg_eq_zero N R _ _ _ halg
   have hN :trdeg k N=n:= by
     dsimp only [N]
     simp [zUx]
   calc
     trdeg k R=trdeg k N+trdeg N R:=(trdeg_add_eq k N (A:=R)).symm
     _=n:= by rw [hN,hzero,add_zero]
private theorem dsT {k B A:Type} [za6 k] [za6 B]
   [ztn B] [za6 A] [zZE B A] {n:ℕ} (q:z3y (Fin n) k →+* A)
   (hC : ∀ a,IsAlgebraic B (q (znf a)))
   (hX : ∀ i,IsAlgebraic B (q (z9v i)))
   (p:z3y (Fin n) k) :IsAlgebraic B (q p) := by
 induction p using MvPolynomial.induction_on with
 | C a=>exact hC a
 | add p r hp hr =>
   rw [map_add]
   exact hp.add hr
 | mul_X p i hp =>
   rw [map_mul]
   exact hp.mul (hX i)
private theorem fV3 (I:znc Ambient) [I.IsPrime]
   (hdim:ringKrullDim (zI I)=2) (f :aZ) (hf :f≠0)
   (hgen:xg I=zye {f}) :
   letI:zZE (Image I) (zI I) :=
     z9T (R:=Image I) (S:=zI I) (aDo I)
   ¬ (IsAlgebraic (Image I) (coord I 2)∧IsAlgebraic (Image I) (coord I 3)) := by
 let B:=Image I
 let A:=zI I
 letI: (xg I).IsPrime :=
   (inferInstance :I.IsPrime).comap AH
 letI:zZE B A:=z9T (R:=B) (S:=A) (aDo I)
 letI:FaithfulSMul B A :=
   (faithfulSMul_iff_algebraMap_injective B A).mpr (enF I)
 letI:zsf FX B A:=zsL (S:=B) (A:=A) fun a=> by
   change zVv I (znf a) =
     zVv I (AH (znf a))
   simp [oi,pZ]
 intro ⟨hy,hv⟩
 have hseed (i:Fin 2) :IsAlgebraic B (coord I (Fin.castLE (by decide :2≤4) i)) := by
   convert isAlgebraic_algebraMap (A:=A) (Ideal.Quotient.mk (xg I) (MvPolynomial.X i)) using 1
   change coord I _=aDo I (Ideal.Quotient.mk (xg I) (MvPolynomial.X i))
   simp [coord,aDo,oi,pZ,RingHom.comp_apply]
 have hcoord (i:Fin 4) :IsAlgebraic B (coord I i) := by
   fin_cases i
   · exact hseed 0
   · exact hseed 1
   · exact hy
   · exact hv
 have hC (a :FX) :IsAlgebraic B (zVv I (znf a)) := by
   change IsAlgebraic B (algebraMap FX A a)
   rw [zG3 FX B A]
   exact isAlgebraic_algebraMap _
 letI:zjH B A:=⟨fun z=> by
   obtain ⟨p,rfl⟩:=zld z
   exact dsT (B:=B) (A:=A) (zVv I) hC hcoord p⟩
 obtain ⟨n,hn,hnt⟩:=cR2 FX B
 obtain ⟨m,hm,hmt⟩:=cR2 FX A
 have htrdeg:=trdeg_add_eq FX B (A:=A)
 rw [trdeg_eq_zero (R:=B) (A:=A),add_zero,hnt,hmt] at htrdeg
 have hnm:n=m:= by exact_mod_cast htrdeg
 have hBA:ringKrullDim B=ringKrullDim A:= by rw [hn,hm,hnm]
 have hle :=ringKrullDim_quotient_succ_le_of_nonZeroDivisor
   (mem_nonZeroDivisors_of_ne_zero hf)
 change ringKrullDim (gk (zye {f}))+1≤ ringKrullDim aZ at hle
 rw [← hgen,hBA,hdim,zmx,
   ringKrullDim_eq_zero_of_field] at hle
 norm_num [zey] at hle
def bff {B A:Type} [za6 B] [za6 A] (i:B →+* A) (y v :A) :
    B[X][X] →+* A[X] :=
  zqf (zhd i) (z1z y+Polynomial.X*z1z v)
private theorem ewF {B A:Type} [za6 B] [ztn B] [Infinite B]
    [za6 A] [zZE B A] (y v :A)
    (h : ¬ (IsAlgebraic B y∧IsAlgebraic B v)) :
    zq4 (bff (algebraMap B A) y v) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  by_contra hp0
  have hex : ∃ j,p.coeff j≠0:= by
    by_contra! h
    exact hp0 (Polynomial.ext fun j=>(h j).trans (zO6 _).symm)
  obtain ⟨j,hj⟩:=hex
  let bad := {c:B | (p.coeff j).IsRoot c}
  have hbad:bad.Finite :=Polynomial.finite_setOfPred_isRoot hj
  obtain ⟨c,hc⟩:=hbad.exists_notMem
  obtain ⟨d,hd⟩:=(hbad.insert c).exists_notMem
  have hdc:d≠c:= fun e=>hd (e ▸ Set.mem_insert c bad)
  have hd' : d∉bad:= fun hb=>hd (Set.mem_insert_of_mem _ hb)
  have alg (b:B) (hb:b∉bad) :IsAlgebraic B (y+b•v) := by
    let q:=p.map (zhy b)
    refine ⟨q,?_,?_⟩
    · intro hz
      apply hb
      change (p.coeff j).eval b=0
      have h:=congrArg (fun z :B[X]=>z.coeff j) hz
      change (p.map (zhy b)).coeff j=(0:B[X]).coeff j at h
      rw [Polynomial.coeff_map,zO6] at h
      exact h
    · let E :=zhy (algebraMap B A b)
      have hcoeff :E.comp (zhd (algebraMap B A)) =
          (algebraMap B A).comp (zhy b) := by
        apply z86
        · intro a
          simp [E,zQb]
        · simp [E,zQb]
      have hs :E (z1z y+Polynomial.X*z1z v)=y+b•v := by
        change (z1z y+Polynomial.X*z1z v).eval
          (algebraMap B A b)=y+b•v
        rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
          zFf,zFf,zd5]
      have H :=congrArg E hp
      change E (p.eval₂ (zhd (algebraMap B A))
        (z1z y+Polynomial.X*z1z v))=E 0 at H
      rw [Polynomial.hom_eval₂,hcoeff,hs,map_zero] at H
      rwa [Polynomial.aeval_def,Polynomial.eval₂_map]
  have hvscaled:=(alg d hd').sub (alg c hc)
  have he : (y+d•v)-(y+c•v)=(d - c)•v := by
    rw [sub_smul]
    abel
  rw [he] at hvscaled
  have hv :=hvscaled.of_smul (mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.mpr hdc))
  have hy :=(alg c hc).sub (hv.smul c)
  rw [add_sub_cancel_right] at hy
  exact h ⟨hy,hv⟩
theorem epI (I:znc Ambient) [I.IsPrime]
  (hdim:ringKrullDim (zI I)=2) (f :aZ) (hf :f≠0)
  (hgen:xg I=zye {f}) :
  zq4 (bff (B:=Image I) (A:=zI I) (aDo I) (coord I 2) (coord I 3)) := by
 letI: (xg I).IsPrime :=
  (inferInstance :I.IsPrime).comap AH
 letI:zZE (Image I) (zI I) :=
    z9T (R:=Image I) (S:=zI I) (aDo I)
 letI:Infinite FX:=Infinite.of_injective _ (zxb L[X] FX)
 letI:Infinite (Image I) :=Infinite.of_injective _ (algebraMap FX (Image I)).injective
 exact ewF _ _ (fV3 I hdim f hf hgen)
end
end aKw
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GK
noncomputable section
open K1 cu gT YY Polynomial
open scoped Polynomial BigOperators
private theorem d01 :FT (B4 0 1)=0:= by
 simp [FT,Fp,B4,zrE]
private def Uj (P:znc aZ) :aQ[X] →ₐ[aQ] SG P :=
 aeval (zVv (i9 P 0 1) (z9v 1))
private theorem cLy (P:znc aZ) :
   (Uj P).comp FT=zvR aQ (i9 P 0 1) := by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · have h:=bNY P 0 1
   simp only [toSlice,coord,z5h,z7N] at h
   simpa [FT,Fp,Uj,sub_eq_iff_eq_add] using h.symm
 · simp [FT,Fp,Uj]
def bfg (P:znc aZ) :
    SG P ≃ₐ[aQ] (aQ[X] ⧸ P.map ajM) := by
  let A:=zvR aQ (i9 P 0 1)
  let B:=zvR aQ (P.map ajM)
  let f :=B.comp FT
  let g:=Uj P
  have hf :i9 P 0 1≤zdq f.toRingHom:= by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (z7X ajM hp)
    · intro p hp
      obtain rfl :=Set.mem_singleton_iff.mp hp
      exact show B (FT (B4 0 1))=0 by rw [d01,map_zero]
  have hg:P.map ajM≤zdq g.toRingHom:= by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    have h:=zmU (cLy P)
      (zDK (algebraMap FX aQ) p)
    refine (show g (ajM p)=A _ from h).trans ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show P.map _≤ i9 P 0 1 from le_sup_left) (z7X _ hp))
  let f' := zTA (i9 P 0 1) f (fun _ hx=>hf hx)
  let g' := zTA (P.map ajM) g (fun _ hx=>hg hx)
  refine AlgEquiv.ofAlgHom f' g' ?_ ?_
  · apply AlgHom.ext
    intro z
    obtain ⟨p,rfl⟩:=zld z
    have hfg:f'.comp g=B:= by
      apply Polynomial.algHom_ext
      simp [f',f,g,Uj,FT,Fp,Ideal.Quotient.liftₐ_apply]
    exact zmU hfg p
  · apply AlgHom.ext
    intro z
    obtain ⟨p,rfl⟩:=zld z
    change g' (f' (zVv (i9 P 0 1) p)) =
      zVv (i9 P 0 1) p
    rw [show f' (zVv (i9 P 0 1) p)=B (FT p) by rfl]
    change (Uj P) (FT p)=zVv (i9 P 0 1) p
    exact zmU (cLy P) p
end
end GK
end
section
namespace aqd
noncomputable section
open K1 cu gT Cu
open scoped Polynomial
def O4 (C₀:sQ) [Fact (Irreducible C₀)] :
    aZ →+* y7 C₀ :=
  zOD (Mr C₀) (Mu C₀ ∘ Wt C₀)
def bv8 (C₀:sQ) [Fact (Irreducible C₀)]
    (h:zdq (O4 C₀)=BI C₀) :
    (aZ ⧸ BI C₀) →+* y7 C₀ :=
  zP2 (BI C₀) (O4 C₀) fun _ hf =>
    RingHom.mem_ker.mp (h.symm ▸ hf)
structure bbr (C₀:sQ) [Fact (Irreducible C₀)] :Prop where
 kernel:zdq (O4 C₀)=BI C₀
 localized:letI:zZE (aZ ⧸ BI C₀) (y7 C₀) :=
  (bv8 C₀ kernel).toAlgebra
  z0o (aZ ⧸ BI C₀) (y7 C₀)
def apf :kM ≃ₐ[FX] aZ[X] :=
 (zGY FX finSuccEquivLast).trans (zpj FX (Fin 2))
end
end aqd
end
section
set_option backward.isDefEq.respectTransparency false
namespace aqd
noncomputable section
open K1 cu gT Cu GK
open scoped Polynomial
private theorem bvb:finSuccEquivLast (0:Fin 3)=some 0:=rfl
private theorem bva :finSuccEquivLast (1 :Fin 3)=some 1 :=rfl
private theorem cfD:finSuccEquivLast (2 :Fin 3)=none :=finSuccEquivLast_last
theorem cfB: (apf.toRingEquiv.toRingHom).comp pZ=Polynomial.C:= by
 apply zXT
 · intro a
   simp [apf,pZ]
 · intro i
   fin_cases i <;> simp [apf,pZ,bvb,bva]
theorem bqA (C₀:sQ) [Fact (Irreducible C₀)] :
   LG C₀ =
    (zhd (O4 C₀)).comp apf.toRingEquiv.toRingHom:= by
 apply zXT
 · intro a
   simp [LG,O4,apf]
 · intro i
   fin_cases i <;> simp [LG,O4,apf,bvb,
    bva,cfD]
theorem d4h (C₀:sQ) [Fact (Irreducible C₀)]
   (hC:bbr C₀) (J:znc kM) (hJ:J.IsPrime)
   (hseed :J.comap pZ=BI C₀) :
   ∃ P:znc (y7 C₀)[X],P.IsPrime∧J=P.comap (LG C₀) := by
 let A:=aZ ⧸ BI C₀
 let:za6 A:=z0w (BI C₀)
 let:za6 A[X] :=zqU
 let u:aZ →+* A:=zVv (BI C₀)
 let φ:A →+* y7 C₀:=bv8 C₀ hC.kernel
 have hφ:φ.comp u=O4 C₀:=RingHom.ext fun _=>rfl
 let: (BI C₀).IsPrime :=hC.kernel ▸ zgL (O4 C₀)
 let:ztn A:=zO0 (BI C₀)
 let:zZE A (y7 C₀) :=φ.toAlgebra
 let:z0o A (y7 C₀) :=hC.localized
 let:zZE A[X] (y7 C₀)[X] :=z88 A (y7 C₀)
 let M:zdT A[X] :=(nonZeroDivisors A).map z1z
 let:zNo M (y7 C₀)[X] :=
   zyz (nonZeroDivisors A) (y7 C₀)
 let e :=apf.toRingEquiv
 let I₀:=J.comap e.symm.toRingHom
 let:I₀.IsPrime :=hJ.comap e.symm.toRingHom
 have hseed' : I₀.comap z1z=BI C₀:= by
   rw [← hseed]
   ext s
   have hcom:e (pZ s)=z1z s :=zmU cfB s
   change e.symm (z1z s)∈J↔pZ s∈J
   rw [← hcom,e.symm_apply_apply]
 let v :=zhd u
 have hv :zpX v :=zMr _ zld
 have hvker :zdq v≤I₀:= by
   change zdq (zhd (zVv (BI C₀)))≤I₀
   rw [zfT,zlC]
   exact Ideal.map_le_iff_le_comap.mpr hseed'.symm.le
 let I:=I₀.map v
 have hI:I.IsPrime :=Ideal.map_isPrime_of_surjective hv hvker
 have hcomap :I.comap v=I₀:= by
   change (I₀.map v).comap v=I₀
   rw [zEk _ hv,← zPx,sup_eq_left.mpr hvker]
 have hdisjoint:Disjoint (M:Set A[X]) (I:Set A[X]) := by
   apply Set.disjoint_left.mpr
   rintro _ ⟨a,ha,rfl⟩ hmem
   obtain ⟨s,rfl⟩:=zld a
   have hs :s∈(I.comap v).comap Polynomial.C:= by
     change v (z1z s)∈I
     simpa only [SetLike.mem_coe,v,u,zKC,zrL] using hmem
   rw [hcomap,hseed'] at hs
   exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (Ideal.Quotient.eq_zero_iff_mem.mpr hs)
 let P:=I.map (algebraMap A[X] (y7 C₀)[X])
 have hP:P.IsPrime :=IsLocalization.isPrime_of_isPrime_disjoint M _ I hI hdisjoint
 have heq :P.comap (zhd φ)=I :=
   IsLocalization.under_map_of_isPrime_disjoint M _ hI hdisjoint
 refine ⟨P,hP,?_⟩
 rw [bqA,← hφ,← zPl,
   ← zg6,← zg6,heq,hcomap]
 ext f
 change f∈J↔e.symm (e f)∈J
 rw [e.symm_apply_apply]
theorem ddp (C₀:sQ) :
  zsE aQ (SG (BI C₀))=C₀.totalDegree := by
 rw [(bfg (BI C₀)).toLinearEquiv.finrank_eq,
  BI,zlN,zyk,finrank_quotient_span_eq_natDegree,
  bO8]
 unfold zph
 rw [zra _ (zyB _)]
theorem ddg (C₀:sQ) (hC:Irreducible C₀) :0<C₀.totalDegree := by
 by_contra! hn
 have h:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (za7 hn)
 have hc:C₀.coeff 0≠0:= by
  intro hz
  exact hC.ne_zero (by simpa [hz] using h)
 exact hC.not_isUnit (h ▸ hc.isUnit.map znf)
end
end aqd
end
section
set_option backward.isDefEq.respectTransparency false
namespace aqd
noncomputable section
open K1 cu gT Cu GK
open scoped Polynomial
def c1 :Prop :=
 ∀ (C₀:sQ) [Fact (Irreducible C₀)],bbr C₀
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM)
    (P:znc (y7 C₀)[X]),bbr C₀ →
    P.IsPrime→J=P.comap (LG C₀) →
    zAa aQ (abX J) →
    0<zsE aQ (abX J) →
    zsE aQ (abX J) =
      zsE aQ (SG (BI C₀)) *
        zsE (y7 C₀) ((y7 C₀)[X] ⧸ P)
theorem eOi (C₀:sQ) [Fact (Irreducible C₀)]
   (f : (y7 C₀)[X]) (hf :f≠0) :
   ∃ q: ((oO C₀)[X])[X],
     q.IsPrimitive∧q.natDegree=f.natDegree∧Associated (q.map (F5 C₀)) f := by
 let:EuclideanDomain (oO C₀)[X] :=zaz
 let:IsPrincipalIdealRing (oO C₀)[X] :=EuclideanDomain.instIsPrincipalIdealRing
 let:UniqueFactorizationMonoid (oO C₀)[X] :=
   PrincipalIdealRing.to_uniqueFactorizationMonoid
 let:StrongNormalizationMonoid (oO C₀)[X] :=
   UniqueFactorizationMonoid.strongNormalizationMonoid
 let:NormalizedGCDMonoid (oO C₀)[X] :=
   UniqueFactorizationMonoid.toNormalizedGCDMonoid _
 let D:=zdR (nonZeroDivisors (oO C₀)[X]) f
 have hinj:=zxb (oO C₀)[X] (y7 C₀)
 obtain ⟨b,hb,hbD⟩ :=
   zXY (nonZeroDivisors (oO C₀)[X]) f
 have he :D.map (F5 C₀)=z1z (F5 C₀ b)*f := by
   exact hbD.trans (zd5 _ _)
 have hbn:F5 C₀ b≠0:= by
   exact (map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hb)
 have hD:D ≠0:= by
   intro hzero
   rw [hzero,Polynomial.map_zero] at he
   exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hbn) hf) he.symm
 have hcontent:F5 C₀ D.content≠0 :=
   (map_ne_zero_iff _ hinj).mpr fun hc=>hD (Polynomial.content_eq_zero_iff.mp hc)
 have hg: (D.map (F5 C₀)).natDegree=f.natDegree := by
   rw [he,Polynomial.natDegree_C_mul hbn]
 have hq:Associated (D.map (F5 C₀)) (D.primPart.map (F5 C₀)) := by
   conv_lhs=>rw [D.eq_C_content_mul_primPart,Polynomial.map_mul,zrL]
   exact associated_unit_mul_left _ _
     ((isUnit_iff_ne_zero.mpr hcontent).map z1z)
 refine ⟨D.primPart,D.isPrimitive_primPart,?_,?_⟩
 · rw [Polynomial.natDegree_primPart,← zt8 hinj D]
   exact hg
 · apply hq.symm.trans
   rw [he]
   exact associated_unit_mul_left _ _ ((isUnit_iff_ne_zero.mpr hbn).map z1z)
theorem of_children (h1 :c1) (h2 :c2) :Cu.c1 := by
  intro C₀ hC J g hJ hseed hfinite hrank hg
  have hCdeg:=ddg C₀ hC.out
  have hpos :0<zsE aQ (abX J) := by
    rw [hrank]
    exact Nat.mul_pos hCdeg hg
  let hbase :=h1 C₀
  obtain ⟨P,hP,hcontract⟩:=d4h C₀ hbase J hJ hseed
  let:P.IsPrime :=hP
  let:EuclideanDomain (y7 C₀)[X] :=zaz
  let:IsPrincipalIdealRing (y7 C₀)[X] :=EuclideanDomain.instIsPrincipalIdealRing
  let:P.IsPrincipal:=IsPrincipalIdealRing.principal P
  let f :=z1N P
  have hfspan:zye {f} = P:=zOZ P
  have hfdeg:f.natDegree=g:= by
    have hquot :
        zsE (y7 C₀) ((y7 C₀)[X] ⧸ P)=f.natDegree := by
      rw [← hfspan,finrank_quotient_span_eq_natDegree]
    have h:=h2 C₀ J P hbase hP hcontract hfinite hpos
    rw [hrank,ddp C₀,hquot] at h
    exact Nat.mul_left_cancel hCdeg h.symm
  have hPne :P ≠ ⊥ := by
    intro hzero
    have hfzero :f=0:=(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mp hzero
    rw [hfzero,Polynomial.natDegree_zero] at hfdeg
    exact (Nat.ne_of_gt hg) hfdeg.symm
  have hfi:Irreducible f :=(Submodule.IsPrincipal.prime_generator_of_isPrime P hPne).irreducible
  obtain ⟨q,hq,hqdeg,hassoc⟩:=eOi C₀ f hfi.ne_zero
  exact ⟨{
    equation :=q
    primitive :=hq
    degree :=hqdeg.trans hfdeg
    irreducible :=hassoc.symm.irreducible hfi
    contraction :=hcontract.trans (congrArg (fun I=>I.comap (LG C₀))
      (hfspan.symm.trans (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)) }⟩
end
end aqd
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace aKw
noncomputable section
open K1 cu gT pI YY aRZ Polynomial
open scoped Polynomial
abbrev Params :=z3y (Fin 4) FX
abbrev aRr (R:Type) [za6 R] :=R[X][X]
private abbrev Triple (R:Type) [za6 R] :=R[X][X][X]
private def constants {R:Type} [za6 R] :R →+* Triple R :=
 Polynomial.C.comp (Polynomial.C.comp z1z)
def J0:aZ →+* Params[X] :=
  zOD (Polynomial.C.comp znf)
    (GK.Fp (z9v 0) (z9v 2))
private def aPe :Params →+* Triple aZ :=
  let x :Fin 4→Triple aZ :=
    ![z7y,z1z (z1z z7y),
      constants (z9v (0:Fin 2) :aZ) +
        z7y*constants (z9v (1 :Fin 2) :aZ),
      z1z z7y]
  zOD ((constants (R:=aZ)).comp (znf:FX →+* aZ)) x
private def aem:Params[X] →+* Triple aZ :=
 zqf aPe (constants (z9v 1))
private def aU3:Triple aZ →+* Params[X] :=
 zqf
  (zqf
    (zqf J0 (z1z (z9v 1)))
    (z1z (z9v 3)))
  (z1z (z9v 0))
private theorem b36 (f :aZ) :
  aU3 (constants f)=J0 f := by
 simp [aU3,constants,zQb]
private theorem ees :aU3.comp aem=RingHom.id _:= by
  have h:aU3.comp aPe=Polynomial.C:= by
    apply zXT
    · intro a
      simp [zQb,aPe,b36,J0]
    · intro i
      fin_cases i <;>
        simp [zQb,aPe,aU3,constants,
          J0,GK.Fp]
      all_goals ring
  apply z86
  · intro a
    simpa [zQb,aem] using zLs h a
  · simp [zQb,aem,b36,J0,
      GK.Fp]
private theorem gB1 (f :aZ) :
    aem (J0 f)=constants f := by
  suffices aem.comp J0=constants by
    exact zLs this f
  apply zXT
  · intro a
    simp [zQb,aem,aPe,J0]
  · intro i
    fin_cases i
    · have h0:J0 (z9v (0:Fin 2)) =
          z1z (z9v 2)-Polynomial.C (z9v 0)*Polynomial.X:= by
        simp [J0,GK.Fp]
      change aem (J0 (z9v (0:Fin 2)))= _
      rw [h0,map_sub aem,map_mul aem]
      simp [aem,aPe]
      exact add_sub_cancel_right (constants (z9v (0:Fin 2) :aZ)) _
    · simp [aem,J0,GK.Fp]
abbrev coords (I:znc Ambient) (i:Fin 4) :aRr (zI I) :=
 z1z (z1z (coord I i))
def ao7 (I:znc Ambient) :Params →+* aRr (zI I) :=
  zOD
    (Polynomial.C.comp (Polynomial.C.comp (algebraMap FX (zI I))))
    ![z7y,z1z z7y,
      coords I 0+Polynomial.X*coords I 1,
      coords I 2+Polynomial.C z7y*coords I 3]
def Qa (I:znc Ambient) :Params[X] →+* aRr (zI I) :=
 zqf (ao7 I) (coords I 1)
private def aX8 (I:znc Ambient) :Triple aZ →+* Triple (Image I) :=
 zhd (zhd (zhd (zVv (xg I))))
private def a9i (I:znc Ambient) :Triple (Image I) →+* aRr (zI I) :=
 zhd
  (bff (B:=Image I) (A:=zI I) (aDo I) (coord I 2) (coord I 3))
private theorem fTP (I:znc Ambient) :
    Qa I=(a9i I).comp ((aX8 I).comp aem) := by
  have h:ao7 I=(a9i I).comp ((aX8 I).comp aPe) := by
    apply zXT
    · intro a
      simp [zQb,ao7,aPe,constants,aX8,
        a9i,bff,aDo,oi,pZ]
      all_goals rfl
    · intro i
      fin_cases i <;>
        simp [zQb,ao7,aPe,constants,aX8,
          a9i,bff,coords,coord,aDo,oi,pZ]
      all_goals ring
  apply z86
  · intro a
    simpa [Qa,zQb,aem] using zLs h a
  · simp [Qa,zQb,aem,constants,aX8,
      a9i,bff,coords,coord,aDo,oi,pZ]
theorem c6Z (I:znc Ambient) [I.IsPrime]
   (hdim:ringKrullDim (zI I)=2) (f :aZ) (hf :f≠0)
   (hgen:xg I=zye {f}) (q:Params[X]) :
   Qa I q=0↔J0 f∣q:= by
 have hinj:zq4 (a9i I) :=
   zTo _ (epI I hdim f hf hgen)
 have hzero (x :Triple (Image I)) :a9i I x=0↔x=0 :=
   ⟨(injective_iff_map_eq_zero _).mp hinj x,fun h=>h.symm ▸ map_zero _⟩
 simp only [fTP,zQb,hzero]
 rw [← (RingHom.mem_ker :aem q∈zdq (aX8 I) ↔
   aX8 I (aem q)=0)]
 rw [aX8,zfT,zfT,
   zfT,zlC,hgen,zlN,zyk,
   zlN,zyk,zlN,zyk]
 change aem q∈(zye {constants f} : znc (Triple aZ))↔J0 f∣q
 rw [Ideal.mem_span_singleton']
 constructor
 · rintro ⟨a,ha⟩
   have h:=congrArg aU3 ha
   rw [map_mul,b36,show aU3 (aem q)=q from
     zLs ees q] at h
   exact ⟨aU3 a,h.symm.trans (mul_comm _ _)⟩
 · rintro ⟨a,ha⟩
   refine ⟨aem a,?_⟩
   rw [ha,map_mul,gB1]
   exact mul_comm (aem a) (constants f)
theorem goo (i:Fin 2) :
  aQa (ek i)=kz (![0,2] i) := by
 unfold ek aQa
 rw [zoc]
 simp [kz]
theorem gon (a :FX) :
  aQa (algebraMap FX aQ a)=algebraMap FX dV a := by
 change aQa (algebraMap aZ aQ (znf a)) =
  algebraMap Params dV (znf a)
 unfold aQa
 rw [zoc]
 simp
theorem c8G (f :aZ) :
    aOQ f =
      zOD (Polynomial.C.comp (algebraMap FX dV))
        (GK.Fp (kz 0) (kz 2)) f := by
  suffices (zhd aQa).comp GK.ajM =
      zOD (Polynomial.C.comp (algebraMap FX dV))
        (GK.Fp (kz 0) (kz 2)) from
    zLs this f
  apply zXT
  · intro a
    simp [zQb,GK.ajM,GK.FT,
      zrE,gon]
  · intro i
    fin_cases i <;>
      simp [zQb,GK.ajM,GK.FT,
        GK.Fp,goo]
theorem bLv (f :aZ) :
    (J0 f).map (algebraMap Params dV)=aOQ f := by
  rw [c8G]
  suffices (zhd (algebraMap Params dV)).comp J0 =
      zOD (Polynomial.C.comp (algebraMap FX dV))
        (GK.Fp (kz 0) (kz 2)) from
    zLs this f
  apply zXT
  · intro a
    simp [zQb,J0]
    all_goals rfl
  · intro i
    fin_cases i <;> simp [J0,GK.Fp,
      kz]
theorem fTS (I:znc Ambient) [I.IsPrime]
  (hdim:ringKrullDim (zI I)=2) (f :aZ) (hf :f≠0)
  (hgen:xg I=zye {f}) :
  zq4 (ao7 I) := by
 have hp:0<(J0 f).natDegree := by
  rw [← zt8 (zxb Params dV),
    bLv,aOQ,
    zt8 aQa.injective,
    GK.bO8]
  by_contra! he
  have he' := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (za7 he)
  have hconst:f.coeff 0≠0:= fun h0=>hf (by simpa [h0] using he')
  have hprime : (xg I).IsPrime :=(inferInstance :I.IsPrime).comap aKw.AH
  have hu:IsUnit f :=he' ▸ hconst.isUnit.map znf
  exact hprime.ne_top (hgen.trans (Ideal.span_singleton_eq_top.mpr hu))
 apply (injective_iff_map_eq_zero _).mpr
 intro d hd
 have hz :Qa I (z1z d)=0:= by simpa [Qa] using hd
 have hdiv :=(c6Z I hdim f hf hgen _).mp hz
 by_contra hn
 have :=Polynomial.natDegree_le_of_dvd hdiv (Polynomial.C_ne_zero.mpr hn)
 simp at this
 omega
end
end aKw
end
section
set_option backward.isDefEq.respectTransparency false
namespace bRL
noncomputable section
open cu Cu aqd
open scoped Polynomial
private abbrev bAA:=z3y (Fin 2) L[X]
private def alV:sQ[X] ≃+* bAA :=
 ((zpj L (Fin 2)).symm.trans
   (zyD L (Fin 2))).toRingEquiv
private theorem b2f (a :sQ) :
    alV (z1z a)=zDK z1z a := by
  have h:alV.toRingHom.comp z1z=zDK Polynomial.C:= by
    apply zXT
    · intro r
      change zyD L (Fin 2)
        ((zpj L (Fin 2)).symm (z1z (znf r)))= _
      simp
    · intro i
      change zyD L (Fin 2)
        ((zpj L (Fin 2)).symm (z1z (z9v i)))= _
      simp
  exact zmU h a
private theorem d3R :
  alV z7y=znf Polynomial.X:= by
 change zyD L (Fin 2)
  ((zpj L (Fin 2)).symm z7y)= _
 simp
private def baseChange :bAA →+* aZ :=
 zDK (algebraMap L[X] FX)
private def aPA (C₀:sQ) :
  sQ[X] →+* (abz C₀)[X] :=
 zhd (zVv (auG C₀))
private def aVn (C₀:sQ) :
   (abz C₀)[X] →+* y7 C₀ :=
 (F5 C₀).comp (zhd
   (algebraMap (abz C₀) (oO C₀)))
private theorem eoY (C₀:sQ) [Fact (Irreducible C₀)] :
   zq4 (aVn C₀) :=
 (zxb (oO C₀)[X] (y7 C₀)).comp
   (zTo _ (zxb
     (abz C₀) (oO C₀)))
private theorem cNX (C₀:sQ) [Fact (Irreducible C₀)] (p:L[X]) :
  Mr C₀ (algebraMap L[X] FX p)=F5 C₀ (p.map (zT C₀)) := by
 unfold Mr IsFractionRing.map
 rw [IsLocalization.map_eq]
 rfl
private theorem cTJ (C₀:sQ) [Fact (Irreducible C₀)] :
    (O4 C₀).comp (baseChange.comp alV.toRingHom) =
      (aVn C₀).comp (aPA C₀) := by
  apply Polynomial.ringHom_ext'
  · apply zXT
    · intro r
      change O4 C₀ (baseChange (alV (z1z (znf r)))) =
        aVn C₀ (aPA C₀ (z1z (znf r)))
      simp [b2f,baseChange,O4,aVn,aPA,
        cNX,zT]
    · intro i
      change O4 C₀ (baseChange (alV (z1z (z9v i)))) =
        aVn C₀ (aPA C₀ (z1z (z9v i)))
      simp [b2f,baseChange,O4,aVn,aPA,
        Mu,Wt]
  · change O4 C₀ (baseChange (alV z7y)) =
      aVn C₀ (aPA C₀ z7y)
    simp [d3R,baseChange,O4,aVn,
      aPA,cNX]
private theorem efS (C₀:sQ) [Fact (Irreducible C₀)] :
    zdq (O4 C₀)=BI C₀:= by
  let:zZE bAA aZ:=z5R
  let M:zdT bAA:=(nonZeroDivisors L[X]).map znf
  let:zNo M aZ:=MvPolynomial.isLocalization (nonZeroDivisors L[X]) FX
  have hk : (zdq (O4 C₀)).comap baseChange =
      (zye {z1z C₀}).map alV.toRingHom:= by
    have h: ((zdq (O4 C₀)).comap baseChange).comap alV.toRingHom =
        zye {z1z C₀} := by
      rw [zEW,zEW,zxS,cTJ,
        zGm _ (eoY C₀),
        aPA,zfT,zlC,zlN,
        zyk]
    rw [← h,zNE alV.toRingHom alV.surjective]
  have hlocal:=zvH M aZ (zdq (O4 C₀))
  change ((zdq (O4 C₀)).comap baseChange).map baseChange =
    zdq (O4 C₀) at hlocal
  rw [← hlocal,hk,z0L,zlN,zyk]
  change zye {baseChange (alV (z1z C₀))} = BI C₀
  rw [b2f]
  simp only [baseChange,BI,MvPolynomial.map_map]
attribute [local instance] Polynomial.algebra in
private theorem eM5 (R F E :Type*) [za6 R] [zrb F] [zrb E]
    [zZE R F] [z0o R F] [zZE F[X] E] [z0o F[X] E]
    (z :E) :
    ∃ a b:R[X],
      z=algebraMap F[X] E (a.map (algebraMap R F)) /
        algebraMap F[X] E (b.map (algebraMap R F)) := by
  let M:zdT R[X] :=(nonZeroDivisors R).map z1z
  let:zNo M F[X] :=zyz (nonZeroDivisors R) F
  obtain ⟨r,s,-,hz⟩:=IsFractionRing.div_surjective F[X] z
  obtain ⟨a,b,d,ha,hb⟩:=IsLocalization.surj₂ M F[X] r s
  let j:=algebraMap F[X] E
  let t:=algebraMap R[X] F[X] (d:R[X])
  have ht:j t≠0:=((IsLocalization.map_units F[X] d).map j).ne_zero
  have ha' : j r*j t=j (a.map (algebraMap R F)) := by
    rw [← map_mul]
    exact congrArg j ha
  have hb' : j s*j t=j (b.map (algebraMap R F)) := by
    rw [← map_mul]
    exact congrArg j hb
  refine ⟨a,b,?_⟩
  rw [← ha',← hb',mul_div_mul_right _ _ ht]
  exact hz.symm
private theorem eQA {R F:Type*} [za6 R] [zrb F]
   (f :R →+* F) (I:znc R) (h:zdq f=I)
   (hfractions : ∀ z :F,∃ a b:R,z=f a/f b) :
   letI:zZE (R ⧸ I) F :=
     (zP2 I f fun _ hr=>RingHom.mem_ker.mp (h.symm ▸ hr)).toAlgebra
   z0o (R ⧸ I) F:= by
 let φ:=zP2 I f fun _ hr=>RingHom.mem_ker.mp (h.symm ▸ hr)
 let:zZE (R ⧸ I) F:=φ.toAlgebra
 have hinj:zq4 φ:=RingHom.lift_injective_of_ker_le_ideal I _ h.le
 let:FaithfulSMul (R ⧸ I) F :=
   (faithfulSMul_iff_algebraMap_injective (R ⧸ I) F).mpr hinj
 change z0o (R ⧸ I) F
 apply IsFractionRing.of_field
 intro z
 obtain ⟨a,b,hz⟩:=hfractions z
 exact ⟨zVv I a,zVv I b,hz⟩
theorem proof :aqd.c1 := by
 intro C₀ hC
 let k :=efS C₀
 refine ⟨k,eQA (O4 C₀) (BI C₀) k ?_⟩
 intro z
 obtain ⟨a,b,hz⟩:=eM5 (abz C₀) (oO C₀)
  (y7 C₀) z
 have hsurj:zpX (aPA C₀) :=
  zMr _ zld
 obtain ⟨a',rfl⟩:=hsurj a
 obtain ⟨b',rfl⟩:=hsurj b
 refine ⟨baseChange (alV a'),baseChange (alV b'),?_⟩
 change z=((O4 C₀).comp (baseChange.comp alV.toRingHom)) a' /
  ((O4 C₀).comp (baseChange.comp alV.toRingHom)) b'
 rw [cTJ]
 exact hz
end
end bRL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace aKw
noncomputable section
open K1 cu gT pI YY aRZ Polynomial
open scoped Polynomial
private abbrev azD (I:znc Ambient) :=
 I.map AU ⊔ zye {JN,Z6}
private abbrev a91 (I:znc Ambient) [I.IsPrime] :=
 FractionRing (aRr (zI I))
private abbrev embed (I:znc Ambient) [I.IsPrime] :
 aRr (zI I) →+* a91 I:=algebraMap _ _
private def coefficients (I:znc Ambient) [I.IsPrime]
  (h:zq4 (ao7 I)) :dV →+* a91 I :=
 zIj (g:=(embed I).comp (ao7 I))
  ((zxb (aRr (zI I)) (a91 I)).comp h)
private theorem bX3 (I:znc Ambient) [I.IsPrime]
  (h:zq4 (ao7 I)) (d:Params) :
  coefficients I h (algebraMap Params dV d)=embed I (ao7 I d) :=
 zoc _ d
private def aNt (I:znc Ambient) [I.IsPrime]
  (h:zq4 (ao7 I)) :PI →+* a91 I :=
 zOD (coefficients I h) (fun i=>embed I (coords I i))
private theorem d1F (I:znc Ambient) [I.IsPrime]
   (h:zq4 (ao7 I)) :
   (aNt I h).comp AU =
     ((embed I).comp (Polynomial.C.comp z1z)).comp (zVv I) := by
 apply zXT
 · intro a
   have ha :algebraMap FX dV a=algebraMap Params dV (znf a) :=rfl
   simp only [zQb,aNt,AU,zpw,
     zTv,ha,bX3,ao7]
   rfl
 · intro i
   simp [aNt,AU,zQb]
private def bsH (I:znc Ambient) [I.IsPrime]
    (h:zq4 (ao7 I)) :Ik I →+* a91 I :=
  zP2 (azD I) (aNt I h) <| by
    change azD I≤zdq (aNt I h)
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro a ha
      change ((aNt I h).comp AU) a=0
      simp [d1F,zQb,Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    · intro a ha
      rcases (show a=JN∨a=Z6 by simpa using ha) with rfl | rfl
      all_goals
        simp [RingHom.mem_ker,JN,Z6,aNt,
          kz,bX3,ao7,coords]
      all_goals ring
private theorem b9j (I:znc Ambient) (a :dV) :
  zVv (azD I) (znf a)=algebraMap dV (Ik I) a := by
 simpa only [zKm] using
  (zOY (R₁:=dV) (azD I) a)
private def XD (I:znc Ambient) :dV[X] →ₐ[dV] Ik I :=
 Polynomial.aeval (zVv (azD I) (z9v 1))
private theorem gn8 (I:znc Ambient) (f :aZ)
    (hf :f∈xg I) :XD I (aOQ f)=0:= by
  let π:=zVv (azD I)
  have hline :π JN=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show zye {JN,Z6} ≤ azD I from le_sup_right)
        (zCn (by simp)))
  have hcoord:π (z9v 0) =
      algebraMap dV (Ik I) (kz 2) -
        algebraMap dV (Ik I) (kz 0)*π (z9v 1) := by
    apply eq_sub_of_add_eq
    apply sub_eq_zero.mp
    simpa only [JN,map_sub,map_add,map_mul,π,b9j] using hline
  have he : (XD I).toRingHom.comp (zOD
      (Polynomial.C.comp (algebraMap FX dV))
      (GK.Fp (kz 0) (kz 2))) =
        (π.comp AU).comp aKw.AH := by
    apply zXT
    · intro a
      simp [zQb,AU,XD,oi,pZ,b9j,π]
    · intro i
      fin_cases i
      · simpa [zQb,AU,XD,oi,pZ,
          GK.Fp] using hcoord.symm
      · simp [zQb,AU,XD,oi,pZ,
          GK.Fp,π]
  rw [c8G]
  exact (zLs he f).trans (Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show I.map AU≤azD I from le_sup_left)
      (z7X AU (show aKw.AH f∈I from hf))))
private theorem gn9 (I:znc Ambient) [I.IsPrime]
   (h:zq4 (ao7 I)) :
   (bsH I h).comp (XD I).toRingHom =
     zqf (coefficients I h) (embed I (coords I 1)) := by
 apply z86
 · intro a
   change bsH I h (XD I (z1z a))= _
   have ha :XD I (z1z a)=algebraMap dV (Ik I) a := by
     simp [ XD]
   rw [ha,← b9j I a]
   simp [bsH,aNt]
 · simp [bsH,aNt,XD,zQb]
theorem proof :aRZ.c1 := by
  intro I hI hdim _ f hf hgen
  let:I.IsPrime :=hI
  have hparam:=fTS I hdim f hf hgen
  have hzF:XD I (aOQ f)=0 :=
    gn8 I f (hgen.symm ▸ z5J f)
  let P:znc dV[X] :=zye {aOQ f}
  let e :=zTA P (XD I) (by
    intro p hp
    exact (Ideal.span_le.mpr (by simpa [RingHom.mem_ker] using hzF) :
      P≤RingHom.ker (XD I).toRingHom) hp)
  refine ⟨e,(injective_iff_map_eq_zero e).mpr ?_⟩
  intro z hz
  obtain ⟨q,rfl⟩:=zld z
  have hz' : XD I q=0:=hz
  have hzero :q.eval₂ (coefficients I hparam) (embed I (coords I 1))=0:= calc
    _=bsH I hparam (XD I q) :=
      (zLs (gn9 I hparam) q).symm
    _=0:= by rw [hz',map_zero]
  let n:=zdR (nonZeroDivisors Params) q
  have hnorm:=IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors Params)
    (coefficients I hparam) q hzero
  have hraw:Qa I n=0:= by
    apply (zxb (aRr (zI I)) (a91 I))
    rw [map_zero]
    have hcomp: (embed I).comp (Qa I) =
        zqf ((coefficients I hparam).comp (algebraMap Params dV))
          (embed I (coords I 1)) := by
      apply z86
      · intro a
        simp [zQb,Qa,bX3]
      · simp [zQb,Qa]
    exact (zLs hcomp n).trans hnorm
  have hdiv :=map_dvd (zhd (algebraMap Params dV))
    ((c6Z I hdim f hf hgen n).mp hraw)
  change (J0 f).map (algebraMap Params dV) ∣
    n.map (algebraMap Params dV) at hdiv
  obtain ⟨d,hd,he⟩:=zXY (nonZeroDivisors Params) q
  change n.map (algebraMap Params dV)=d•q at he
  rw [bLv,he,zd5,zG3 Params dV,
    zrE] at hdiv
  have hdunit :IsUnit (algebraMap Params dV d) :=isUnit_iff_ne_zero.mpr (by
    simpa using (zxb Params dV).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp hd))
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ((hdunit.map z1z).dvd_mul_left.mp hdiv))
end
end aKw
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace aR0
noncomputable section
open Polynomial
open scoped BigOperators Polynomial
private theorem bp9 (e :Fin 2 →₀ ℕ) :e.sum (fun _ m=>m)=e 0+e 1 := by
 simp [zWf e (ziq e.support)]
def J0 {F:Type} [zrb F] :
    z3y (Fin 2) F →+* (z3y (Fin 2) F)[X] :=
  zOD (Polynomial.C.comp (znf:F →+* z3y (Fin 2) F))
    (GK.Fp (R:=z3y (Fin 2) F) (z9v 0) (z9v 1))
private theorem bIv {R:Type} [za6 R] (s t:R) :
  (GK.Fp s t 0).natDegree≤1 := by
 change (z1z t - z1z s*(z7y:R[X])).natDegree≤1
 have hs : (z1z s*(z7y:R[X])).natDegree≤1 := by
  simpa only [pow_one] using natDegree_C_mul_X_pow_le s 1
 exact (natDegree_sub_le _ _).trans (max_le (by simp) hs)
private theorem bXM {F:Type} [zrb F]
   (e :Fin 2 →₀ ℕ) (a :F) (d:ℕ)
   (he :e 0+e 1≤d) :
   (J0 (ztt e a)).coeff d =
     if e 0+e 1=d then znf a*(-MvPolynomial.X 0)^e 0 else 0:= by
 let q: (z3y (Fin 2) F)[X] :=
   GK.Fp (R:=z3y (Fin 2) F) (z9v 0) (z9v 1) 0
 have hq:q.natDegree≤1 :=bIv _ _
 have hcoeff :q.coeff 1 = -(z9v 0:z3y (Fin 2) F) := by simp [q,GK.Fp,coeff_sub]
 have hpow: (q^e 0).natDegree≤e 0:= by simpa using natDegree_pow_le_of_le (e 0) hq
 have hXpow: ((z7y: (z3y (Fin 2) F)[X])^e 1).natDegree≤e 1 := by simp
 have hqpow: (q^e 0).coeff (e 0)=(-(z9v 0:z3y (Fin 2) F))^e 0:= by
   simpa [hcoeff] using (coeff_pow_of_natDegree_le (m:=e 0) hq)
 rw [zXU,map_mul,map_mul,map_pow,map_pow]
 simp only [J0,GK.Fp,zTv,zrD,
   zQb,zbs,z87]
 change ((z1z (znf a)*q^e 0)*z7y ^e 1).coeff d= _
 rw [mul_assoc,coeff_C_mul]
 split_ifs with heq
 · rw [← heq,coeff_mul_add_eq_of_natDegree_le hpow hXpow,hqpow,coeff_X_pow_self]
   simp
 · rw [coeff_eq_zero_of_natDegree_lt,mul_zero]
   exact (natDegree_mul_le_of_le hpow hXpow).trans_lt (lt_of_le_of_ne he heq)
theorem dMs {F:Type} [zrb F]
    {g:z3y (Fin 2) F} (hg:g≠0) :
    (J0 g).coeff g.totalDegree≠0:= by
  classical
  let d:=g.totalDegree
  obtain ⟨e,he,hde⟩:=zOU g.support
    (MvPolynomial.support_nonempty.mpr hg) (fun e=>e.sum (fun _ m=>m))
  change d=e.sum (fun _ m=>m) at hde
  rw [bp9] at hde
  have hh (e' : Fin 2 →₀ ℕ) (he' : e' ∈ g.support) :e' 0+e' 1≤d:= by
    rw [← bp9]
    exact zY3 he'
  have hexp :
      (J0 g).coeff d =
        ∑ e' ∈ g.support with e' 0+e' 1=d,
          znf (g.coeff e')*(-MvPolynomial.X 0)^e' 0:= by
    conv_lhs=>rw [g.as_sum]
    rw [map_sum,finsetSum_coeff,zLJ]
    exact zUp rfl (fun e' he' =>
      bXM e' (g.coeff e') d (hh e' he'))
  have hcoef (a :F) (k m:ℕ) :
      (znf a*(-(z9v 0: (z3y (Fin 2) F)))^k).coeff (zhf 0 m)
        = if k=m then a*(-1)^k else 0:= by
    have hneg: (znf (-1 :F) : (z3y (Fin 2) F)) = -1 :=
      (map_neg (znf:F →+* (z3y (Fin 2) F)) 1).trans
        (congrArg Neg.neg (map_one (znf:F →+* (z3y (Fin 2) F))))
    have hn : -(z9v 0: (z3y (Fin 2) F))=znf (-1 :F)*z9v 0 :=
      (neg_one_mul (z9v 0: (z3y (Fin 2) F))).symm.trans
        (congrArg (fun z=>z*(z9v 0: (z3y (Fin 2) F))) hneg.symm)
    rw [hn,mul_pow,← map_pow,← mul_assoc,← map_mul,z06,
      zp9,z0I]
    by_cases hk :k=m
    · simp [hk]
    · have hs :zhf (0:Fin 2) k≠zhf 0 m:= by
        intro h
        exact hk (by simpa using zmU h 0)
      simp [hk,hs]
  intro ht
  have hz :=congrArg (fun f : (z3y (Fin 2) F)=>f.coeff (zhf 0 (e 0))) ht
  rw [hexp] at hz
  simp only [zqN,AddMonoidAlgebra.coeff_zero,hcoef] at hz
  rw [zi6 e] at hz
  · have hz' : g.coeff e*(-1 :F)^e 0=0:= by simpa using hz
    exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp he)
      (pow_ne_zero (e 0) (neg_ne_zero.mpr one_ne_zero))) hz'
  · intro e' he' hne
    have hdiff :e' 0≠e 0:= by
      intro h0
      have h1 :e' 1=e 1 := by
        have :=(Finset.mem_filter.mp he').2
        omega
      exact hne (Finsupp.ext (by intro i; fin_cases i <;> assumption))
    simp [hdiff]
  · exact fun h=>False.elim (h (Finset.mem_filter.mpr ⟨he,hde.symm⟩))
end
end aR0
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace bzY
noncomputable section
open K1 cu gT GK Cu aqd
open scoped Polynomial
local instance (I:znc aZ) :za6 (gk I)[X] :=
 @zqU (gk I) (z0w I)
private theorem c4e (I:znc aZ) (x :SG I) :
    ∃ (q: (gk I)[X]) (d:aZ),d∈nonZeroDivisors aZ ∧
      x*algebraMap aQ (SG I) (algebraMap aZ aQ d) =
        vV I 0 1 q:= by
  let:zZE (z3y (Fin 2) aZ) (Over 2) :=z5R
  obtain ⟨f,rfl⟩:=zld x
  obtain ⟨⟨g,m⟩,hgm⟩:=zg4
    (M:=(nonZeroDivisors aZ).map (znf (σ:=Fin 2))) f
  obtain ⟨d,hd,hdm⟩:=m.property
  let lift:z3y (Fin 2) aZ →+* (gk I)[X] :=
    zOD (qw I 0 1) (fun k=>z1z (coord I k))
  have hcomp: (vV I 0 1).comp lift =
      (zVv (i9 I 0 1)).comp
        (zDK (algebraMap aZ aQ)) := by
    apply zXT
    · intro a
      simp only [zQb,lift,zTv,zpw]
      rw [← zKm,zOY]
      exact zLs (aEa I 0 1) a
    · intro k
      simp [lift,vV,toSlice,zQb]
  have hgm' : f*znf (algebraMap aZ aQ d) =
      zDK (algebraMap aZ aQ) g:= by
    simpa only [zu9,← hdm,zpw] using hgm
  refine ⟨lift g,d,hd,?_⟩
  calc
    _=zVv (i9 I 0 1) (f*znf (algebraMap aZ aQ d)) :=
      (map_mul _ _ _).symm
    _ = _:=(congrArg (zVv (i9 I 0 1)) hgm').trans
      (zLs hcomp g).symm
private theorem eLO (I:znc aZ) [I.IsPrime] [Nontrivial (SG I)] :
    ztn (SG I) := by
  let:ztn (gk I) :=zO0 I
  let scale :aZ →+* SG I :=
    (algebraMap aQ (SG I)).comp (algebraMap aZ aQ)
  have numerator_ne (x :SG I) (hx :x≠0) (q: (gk I)[X]) (d:aZ)
      (hd:d∈nonZeroDivisors aZ) (he :x*scale d=vV I 0 1 q) :
      q≠0:= by
    intro hq
    rw [hq,map_zero] at he
    have hd' : algebraMap aZ aQ d≠0 :=
      (map_ne_zero_iff _ (zxb aZ aQ)).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp hd)
    have hu:IsUnit (scale d) :=
      ((isUnit_iff_ne_zero.mpr hd').map (algebraMap aQ (SG I)))
    exact hx (hu.mul_right_cancel (he.trans (zero_mul _).symm))
  let:NoZeroDivisors (SG I) :=⟨by
    intro x y h
    by_contra! hne
    obtain ⟨q,d,hd,hq⟩:=c4e I x
    obtain ⟨r,e,he,hr⟩:=c4e I y
    have hprod:vV I 0 1 (q*r)=0:= by
      calc
        _=(x*scale d)*(y*scale e) := by
          rw [map_mul,← hq,← hr]
          rfl
        _=(x*y)*(scale d*scale e) :=mul_mul_mul_comm x (scale d) y (scale e)
        _=0:= by rw [h,zero_mul]
    exact (mul_ne_zero (numerator_ne x hne.1 q d hd hq) (numerator_ne y hne.2 r e he hr))
      ((injective_iff_map_eq_zero _).mp (aQr I 0 1) _ hprod)⟩
  exact NoZeroDivisors.to_isDomain _
theorem eLP (C₀:sQ) [h:Fact (Irreducible C₀)] (hC:bbr C₀) :
  IsField (SG (BI C₀)) := by
 have hpos :0<zsE aQ (SG (BI C₀)) := by
  rw [ddp]
  exact ddg C₀ h.out
 let: (BI C₀).IsPrime :=hC.kernel ▸ zgL (O4 C₀)
 let:Nontrivial (SG (BI C₀)) :=zcE hpos
 let:ztn (SG (BI C₀)) :=eLO (BI C₀)
 let:zAa aQ (SG (BI C₀)) :=Module.finite_of_finrank_pos hpos
 exact isField_of_isIntegral_of_isField' (S:=SG (BI C₀))
  (Field.toIsField aQ)
theorem gBU (I:znc aZ) [I.IsPrime] [Nontrivial (SG I)] :
  zq4 (toSlice I 0 1) := by
 intro a b hab
 apply zmy
 apply aQr I 0 1
 simpa [vV] using hab
end
end bzY
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace aR0
noncomputable section
open cu gT pI ac2 Polynomial
open scoped Polynomial
private abbrev aAY (I:znc Ambient) :=
 zM1 (z3y (Fin 2) (Tw I))
private abbrev aSc (I:znc Ambient) :=FractionRing (aAY I)
private def arD (I:znc Ambient) (i:Fin 2) :Tw I :=
 avd I (z9v i)
private def cbg:Fin 4 ≃ Fin 4 where
 toFun := ![2,0,3,1]
 invFun := ![1,3,0,2]
 left_inv := by intro i; fin_cases i <;> rfl
 right_inv := by intro i; fin_cases i <;> rfl
private def ahq (I:znc Ambient) :
    z3y (Fin 3) FX →+* aAY I :=
  zOD
    (Polynomial.C.comp (MvPolynomial.C.comp ((avd I).comp znf)))
    ![z1z (znf (arD I 0)) +
        z7y*z1z (znf (arD I 1)),
      z1z (z9v 0),z1z (z9v 1)]
private theorem dMU {I:znc Ambient} (hI:xN I)
    [(I.comap qO).IsPrime] :
    zq4 (constantCoeff.comp (ahq I)) := by
  let a :FX[X] →+* Tw I :=
    (algebraMap (agI I) (Tw I)).comp (aD4 I).toRingHom
  have ha :zq4 a :=
    (zxb (agI I) (Tw I)).comp (c2Q hI)
  have aC (c:FX) :a (z1z c)=avd I (znf c) := by
    change (algebraMap (agI I) (Tw I)) (aD4 I (z1z c))= _
    rw [aD4,Polynomial.aeval_C]
    rfl
  have aX:a z7y=arD I 0:= by
    change (algebraMap (agI I) (Tw I)) (aD4 I z7y)= _
    rw [aD4,Polynomial.aeval_X]
    rfl
  let b:=(zGY FX (finSuccEquiv 2)).trans
    (zyD FX (Fin 2))
  have he :constantCoeff.comp (ahq I) =
      (zDK a).comp b.toRingHom:= by
    apply zXT
    · intro c
      change constantCoeff (ahq I (znf c)) =
        zDK a (b (znf c))
      simp only [ahq,zTv,zQb,
        constantCoeff_apply,coeff_C_zero,b,AlgEquiv.trans_apply,
        zyl,zt1,
        MvPolynomial.optionEquivRight_C,zpw,aC]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change constantCoeff (ahq I (z9v 0)) =
          zDK a (b (z9v 0))
        simp only [ahq,zrD,zbs,
          constantCoeff_apply,coeff_add,mul_coeff_zero,coeff_C_zero,coeff_X_zero,zero_mul,
          add_zero,b,AlgEquiv.trans_apply,zyl,z6l,
          finSuccEquiv_zero,MvPolynomial.optionEquivRight_X_none,zpw,aX]
      · change constantCoeff (ahq I (z9v j.succ)) =
          zDK a (b (z9v j.succ))
        simp only [ahq,zrD,b,AlgEquiv.trans_apply,
          zyl,z6l,finSuccEquiv_succ,
          MvPolynomial.optionEquivRight_X_some,z7N]
        fin_cases j <;> simp
  rw [he]
  exact (zNV _ ha).comp b.injective
private theorem d1N {A B:Type*} [za6 A] [za6 B]
   [ztn B] (f :A →+* B[X]) (hf :zq4 (constantCoeff.comp f)) :
   zq4 (eval₂RingHom f z7y) := by
 let e :=eval₂RingHom f z7y
 have he :constantCoeff.comp e=(constantCoeff.comp f).comp constantCoeff := by
   apply z86
   · intro c
     simp [e]
   · simp [e]
 apply (zli e).2
 rw [RingHom.ker_eq_bot_iff_eq_zero]
 intro q
 induction q using Polynomial.recOnHorner with
 | M0=>simp
 | MC q a hq ha _ =>
   intro hz
   have hc:=zLs he (q+Polynomial.C a)
   change constantCoeff (e (q+Polynomial.C a))=(constantCoeff.comp f) ((q+Polynomial.C a).coeff 0) at hc
   rw [hz,map_zero,coeff_add,hq,coeff_C_zero,zero_add] at hc
   exact (ha (hf (hc.symm.trans (map_zero _).symm))).elim
 | MX q _ ih =>
   intro hz
   have hX:e z7y=Polynomial.X:= by simp [e]
   rw [map_mul,hX] at hz
   rw [ih ((mul_eq_zero.mp hz).resolve_right X_ne_zero),zero_mul]
private def bNr (I:znc Ambient) :
   z3y (Fin 4) FX →+* aAY I :=
 (eval₂RingHom (ahq I) z7y).comp
   ((z8s FX 3).toRingHom.comp (zGY FX cbg).toRingHom)
private theorem gnA {I:znc Ambient} (hI:xN I)
   [(I.comap qO).IsPrime] :zq4 (bNr I) :=
 (d1N _ (dMU hI)).comp
   ((z8s FX 3).injective.comp (zGY FX cbg).injective)
private def bv3 {I:znc Ambient} (hI:xN I)
  [(I.comap qO).IsPrime] :dV →+* aSc I :=
 zIj (K:=dV)
  (g:=(algebraMap (aAY I) (aSc I)).comp (bNr I))
  ((zxb (aAY I) (aSc I)).comp (gnA hI))
private def Bg (I:znc Ambient) :
   z3y (Fin 2) (Tw I) →+* aSc I :=
 (algebraMap (aAY I) (aSc I)).comp z1z
private theorem gno {I:znc Ambient} (hI:xN I)
   [(I.comap qO).IsPrime] (c:FX) :
   bv3 hI (algebraMap FX dV c) =
     Bg I (znf (avd I (znf c))) := by
 rw [zG3 FX (z3y (Fin 4) FX) dV]
 simp [bv3,bNr,ahq,Bg,zyf]
private theorem gnz (I:znc Ambient) (i:Fin 4) :
    bNr I (z9v i) =
      ![z1z (z9v 0),z7y,z1z (z9v 1),
        z1z (znf (arD I 0)) +
          z7y*z1z (znf (arD I 1))] i:= by
  change eval₂RingHom (ahq I) z7y
    (z8s FX 3 (zGY FX cbg (z9v i)))= _
  rw [zyl,z6l]
  fin_cases i
  · change eval₂RingHom (ahq I) z7y
      (z8s FX 3 (z9v (1 :Fin 3).succ))= _
    rw [z07]
    simp [ahq]
  · change eval₂RingHom (ahq I) z7y
      (z8s FX 3 (z9v 0))= _
    rw [zOO]
    simp
  · change eval₂RingHom (ahq I) z7y
      (z8s FX 3 (z9v (2 :Fin 3).succ))= _
    rw [z07]
    simp [ahq]
  · change eval₂RingHom (ahq I) z7y
      (z8s FX 3 (z9v (0:Fin 3).succ))= _
    rw [z07]
    simp [ahq]
private theorem bNq {I:znc Ambient} (hI:xN I)
    [(I.comap qO).IsPrime] (i:Fin 4) :
    bv3 hI (kz i) =
      ![Bg I (z9v 0),algebraMap (aAY I) (aSc I) z7y,
        Bg I (z9v 1),
        Bg I (znf (arD I 0))+algebraMap (aAY I) (aSc I) z7y *
          Bg I (znf (arD I 1))] i:= by
  unfold bv3 kz
  rw [zoc,zQb,gnz]
  fin_cases i <;> simp [Bg,zQb]
  exact mul_comm _ _
set_option maxHeartbeats 2000000 in
theorem dVu {I:znc Ambient} (hI:xN I)
    (g:z3y (Fin 2) (Tw I)) (hg:g≠0)
    (hIg:I.map (T3 I)=zye {g}) :
    g.totalDegree≤zsE dV (Ik I) := by
  classical
  let:I.IsPrime :=hI.prime
  let: (I.comap qO).IsPrime :=Ideal.comap_isPrime qO I
  let:zAa dV (Ik I) :=hI.bfE
  let L:=aSc I
  let b:=Bg I
  let s :=bv3 hI
  let T:=(zhd b).comp J0
  let q:=T g
  let V:=AdjoinRoot q
  let e :PI →+* L[X] :=
    zOD (Polynomial.C.comp s)
      ![z1z (b (z9v 1))-Polynomial.C (b (z9v 0))*z7y,
        z7y,z1z (b (znf (arD I 0))),
        z1z (b (znf (arD I 1)))]
  have heC (c:dV) :e (znf c)=z1z (s c) := by
    simp only [e,zTv,zQb]
    rfl
  have hTC (c:Tw I) :T (znf c)=z1z (b (znf c)) := by
    change (J0 (znf c)).map b= _
    simp [J0]
  have hTX (j:Fin 2) :T (z9v j) =
      (GK.Fp (R:=z3y (Fin 2) (Tw I))
        (z9v 0) (z9v 1) j).map b:= by
    change (J0 (z9v j)).map b= _
    rw [J0,zrD]
  have hcomm:e.comp AU=T.comp (T3 I) := by
    apply zXT
    · intro c
      change e (zDK _ (znf c)) =
        T (Ih (avd I) (znf c))
      rw [zpw,bOe,hTC,heC]
      exact congrArg z1z (gno hI c)
    · intro i
      obtain ⟨j | j,rfl⟩:=(finSumFinEquiv (m:=2) (n:=2)).surjective i
      · rw [finSumFinEquiv_apply_left]
        change e (zDK _ (z9v (Fin.castAdd 2 j))) =
          T (Ih (avd I) (z9v (Fin.castAdd 2 j)))
        rw [z7N,bOg,hTX]
        fin_cases j <;> simp [e,GK.Fp]
      · rw [finSumFinEquiv_apply_right]
        change e (zDK _ (z9v (Fin.natAdd 2 j))) =
          T (Ih (avd I) (z9v (Fin.natAdd 2 j)))
        rw [z7N,bwR,hTC]
        fin_cases j <;> simp [e,arD] <;> rfl
  have hs0:s (kz 0)=b (z9v 0) :=bNq hI 0
  have hs2 :s (kz 2)=b (z9v 1) :=bNq hI 2
  have hs1 :s (kz 1)=algebraMap (aAY I) L Polynomial.X :=
    bNq hI 1
  have hs3 :s (kz 3)=b (znf (arD I 0)) +
      algebraMap (aAY I) L z7y*b (znf (arD I 1)) :=
    bNq hI 3
  have hseed :e JN=0:= by
    simp only [JN,map_sub,map_add,map_mul,heC,hs0,hs2]
    simp [e]
  have hjet:e Z6=0:= by
    have hy :e (z9v 2)=z1z (b (znf (arD I 0))) := by
      simp [e]
      rfl
    have hv :e (z9v 3)=z1z (b (znf (arD I 1))) := by
      simp [e]
      rfl
    rw [Z6,map_sub e,map_add e,map_mul e,heC (kz 1),
      heC (kz 3),hs1,hs3,hy,hv,Polynomial.C_add,Polynomial.C_mul,sub_self]
  let H :=I.map AU ⊔ zye {JN,Z6}
  let v :PI →+* V:=(AdjoinRoot.mk q).comp e
  have hker :H≤zdq v := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro f hf
      have hm:=z7X (T3 I) hf
      rw [hIg,Ideal.mem_span_singleton] at hm
      apply RingHom.mem_ker.mpr
      change AdjoinRoot.mk q ((e.comp AU) f)=0
      rw [hcomm]
      exact AdjoinRoot.mk_eq_zero.mpr (map_dvd T hm)
    · intro f hf
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · apply RingHom.mem_ker.mpr
        change AdjoinRoot.mk q (e JN)=0
        rw [hseed,map_zero]
      · apply RingHom.mem_ker.mpr
        change AdjoinRoot.mk q (e Z6)=0
        rw [hjet,map_zero]
  let F:Ik I →+* V:=zP2 H v fun _ hf=>RingHom.mem_ker.mp (hker hf)
  let x :Ik I:=zVv H (z9v 1)
  have hx :F x=AdjoinRoot.root q:= by
    change zP2 H v _ (zVv H (z9v 1))= _
    rw [z0R]
    change AdjoinRoot.mk q (e (z9v 1))= _
    rw [show e (z9v 1)=z7y by simp [e],AdjoinRoot.mk_X]
  have hc (c:dV) :F (algebraMap dV (Ik I) c) =
      algebraMap L V (s c) := by
    change zP2 H v _ (zVv H (znf c))= _
    rw [z0R]
    change AdjoinRoot.mk q (e (znf c))= _
    rw [heC]
    exact AdjoinRoot.mk_C (s c)
  have hcoeff :q.coeff g.totalDegree≠0:= by
    change ((J0 g).map b).coeff _≠0
    rw [coeff_map]
    exact fun h=>dMs hg
      ((zxb (aAY I) L).comp zmy
        (h.trans (map_zero b).symm))
  have hq:q≠0:= fun h=>hcoeff (by simp [h])
  have hpow:z14 L (fun i:Fin q.natDegree=>AdjoinRoot.root q^(i:ℕ)) := by
    let P:=AdjoinRoot.powerBasis hq
    have hP:z14 L (fun i:Fin q.natDegree=>P.basis i) :=
      P.basis.linearIndependent
    have heq : (fun i:Fin q.natDegree=>P.basis i) =
        (fun i:Fin q.natDegree=>AdjoinRoot.root q^(i:ℕ)) :=
      funext (fun i=>P.basis_eq_pow i)
    exact heq ▸ hP
  have hlin:z14 dV (fun i:Fin q.natDegree=>x^(i:ℕ)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hh:=congrArg F ha
    simp only [map_sum,zd5,map_mul,map_pow,hx,hc,map_zero] at hh
    have hz :=Fintype.linearIndependent_iff.mp hpow (fun j=>s (a j))
      (by simpa only [zd5] using hh) i
    exact s.injective (hz.trans (map_zero s).symm)
  exact (le_natDegree_of_ne_zero hcoeff).trans (by simpa using hlin.fintype_card_le_finrank)
end
end aR0
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace cyZ
noncomputable section
open K1 cu gT pI YY
open scoped nonZeroDivisors
private abbrev IW (k :Type) [za6 k] :=z3y (Fin 2) k
private theorem d2R {k :Type} [za6 k] (a b y v :k)
    (f :z3y (Fin 2) k) :
    zY9 ![a,b,y,v]
      (MvPolynomial.rename (Fin.castLE (by decide :3≤4))
        (MvPolynomial.rename (Fin.castLE (by decide :2≤3)) f)) =
      zY9 ![a,b] f := by
  let cast34 :=zQY (by decide :3≤4)
  let cast23:=zQY (by decide :2≤3)
  rw [zCp,zCp]
  have hvec: (![a,b,y,v] ∘ cast34) ∘ cast23 = ![a,b] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
private theorem dcM {I:znc Ambient} {z :K} {R:zM1 K}
  (hm: (xg I).IsMaximal) (hmark :IZ I z R) :
  xg I=zdq (qD z) := by
 apply hm.eq_of_le (zZK (qD z))
 intro f hf
 have hmem: (oi.comp pZ) f∈I:=hf
 have he :aci z R ((oi.comp pZ) f)=qD z f :=
  d2R (jz z) (jz z^p) (kr R) (kr R.derivative) f
 exact RingHom.mem_ker.mpr (he.symm.trans (RingHom.mem_ker.mp (hmark hmem)))
private theorem got {I:znc Ambient} {z :K} {R:zM1 K}
  (hm: (xg I).IsMaximal) (hmark :IZ I z R) :
  (z9v 0-MvPolynomial.C (jz z) :Ambient)∈I ∧
  (z9v 1-MvPolynomial.C (jz z^p) :Ambient)∈I:= by
 have h₀: (z9v 0-MvPolynomial.C (jz z) :aZ)∈xg I:= by
  rw [dcM hm hmark]
  exact RingHom.mem_ker.mpr (by simp [qD])
 have h₁: (z9v 1-MvPolynomial.C (jz z^p) :aZ)∈xg I:= by
  rw [dcM hm hmark]
  exact RingHom.mem_ker.mpr (by simp [qD])
 have brQ (f :aZ) (hf :f∈xg I) :oi (pZ f)∈I:=hf
 exact ⟨by simpa [oi,pZ] using brQ _ h₀,
  by simpa [oi,pZ] using brQ _ h₁⟩
private def beM {k :Type} [za6 k] :IW k →+* z3y (Fin 4) k :=
 zOD znf ![z9v 2,z9v 3]
private def ars {k :Type} [za6 k] (a b:k) :z3y (Fin 4) k →+* IW k :=
 zOD znf
  ![znf a,znf b,z9v 0,z9v 1]
private theorem ecJ {k :Type} [zrb k] {I:znc (z3y (Fin 4) k)}
   (hdim:ringKrullDim (gk I)=2) {a b:k}
   (h₀:z9v 0-MvPolynomial.C a∈I)
   (h₁:z9v 1-MvPolynomial.C b∈I) :
   I≤zdq (ars a b) := by
 let q:z3y (Fin 4) k →+* gk I:=zVv I
 let j:IW k →+* gk I:=q.comp beM
 have q₀:q (z9v 0)=q (znf a) := by
   apply sub_eq_zero.mp
   rw [← map_sub]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr h₀
 have q₁:q (z9v 1)=q (znf b) := by
   apply sub_eq_zero.mp
   rw [← map_sub]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr h₁
 have hcomp:j.comp (ars a b)=q:= by
   apply zXT
   · intro c
     simp [j,beM,ars]
   · intro i
     fin_cases i
     · simpa [j,beM,ars] using q₀.symm
     · simpa [j,beM,ars] using q₁.symm
     · simp [j,beM,ars]
     · simp [j,beM,ars]
 have hsurj:zpX j:= by
   intro x
   obtain ⟨f,rfl⟩:=(zld (I:=I)) x
   exact ⟨ars a b f,zLs hcomp f⟩
 have hplane :ringKrullDim (IW k)=2 := by
   rw [zmx,ringKrullDim_eq_zero_of_field]
   norm_num [zey]
 have hinj:zq4 j:= by
   apply (injective_iff_map_eq_zero j).mpr
   intro f hjf
   by_contra hf
   have hreg:f∈(IW k)⁰:=mem_nonZeroDivisors_of_ne_zero hf
   have hle :=ringKrullDim_succ_le_of_surjective j hsurj hreg hjf
   rw [hdim,hplane] at hle
   norm_num at hle
 intro f hf
 apply RingHom.mem_ker.mpr
 apply hinj
 rw [map_zero]
 change (j.comp (ars a b)) f=0
 rw [hcomp]
 exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
private theorem epY (I:znc Ambient) [zAa aQ (Lj I)]
    (a b:FX) (hI:I≤zdq (ars a b)) :0<pN I 3:= by
  let e :vR →+* aQ :=
    zY9 ![algebraMap FX aQ a,algebraMap FX aQ b]
  have hC (c:FX) :
      algebraMap (IW FX) aQ (znf c)=algebraMap FX aQ c:= by
    rw [zG3 FX (IW FX) aQ,zKm]
  have hcomp :
      e.comp CG=(algebraMap (IW FX) aQ).comp (ars a b) := by
    apply zXT
    · intro c
      simp only [zQb,CG,ars,zTv,e,
        z9X,hC]
    · intro i
      simp only [zQb,CG,ars,zrD]
      fin_cases i
      · change e (z9v 0)=algebraMap (IW FX) aQ (znf a)
        rw [hC]
        exact zV6 0
      · change e (z9v 1)=algebraMap (IW FX) aQ (znf b)
        rw [hC]
        exact zV6 1
      · change e (znf (ek 0))=ek 0
        exact z9X (ek 0)
      · change e (znf (ek 1))=ek 1
        exact z9X (ek 1)
  have hm:I.map CG≤zdq e := by
    rw [zo0,zEW,hcomp]
    intro f hf
    apply RingHom.mem_ker.mpr
    change algebraMap (IW FX) aQ (ars a b f)=0
    rw [RingHom.mem_ker.mp (hI hf),map_zero]
  have hn:I.map CG ≠ ⊤ := fun ht =>
    zZK e (top_unique (ht ▸ hm))
  let:Nontrivial (Lj I) :=Ideal.Quotient.nontrivial_iff.mpr hn
  change 0<zsE aQ (Lj I)
  exact (Module.finrank_pos_iff_of_free aQ (Lj I)).mpr inferInstance
theorem proof :aRZ.c2 := by
 intro I _ hdim hm hfinite hmark
 let:zAa aQ (Lj I) :=hfinite
 obtain ⟨z,R,hon⟩:=hmark
 obtain ⟨h₀,h₁⟩:=got hm hon
 exact epY I _ _ (ecJ hdim h₀ h₁)
end
end cyZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace bzY
noncomputable section
open K1 cu gT GK Cu aqd
open scoped Polynomial
local instance (I:znc aZ) :za6 (SG I)[X] :=
 @zqU (SG I) (z0w (i9 I 0 1))
private def Ot (R:Type) [za6 R] :
   z3y (Fin 3) R ≃ₐ[R] (z3y (Fin 2) R)[X] :=
 (zGY R finSuccEquivLast).trans (zpj R (Fin 2))
private theorem bvb:finSuccEquivLast (0:Fin 3)=some 0:=rfl
private theorem bva :finSuccEquivLast (1 :Fin 3)=some 1 :=rfl
private theorem cfD:finSuccEquivLast (2 :Fin 3)=none :=finSuccEquivLast_last
private abbrev incl (R:Type) [za6 R] :
   z3y (Fin 2) R →+* z3y (Fin 3) R :=
 (zHw (zQY (by decide :2≤3))).toRingHom
private theorem fXT (R:Type) [za6 R] :
   (Ot R).toRingEquiv.toRingHom.comp (incl R)=Polynomial.C:= by
 apply zXT
 · intro a
   simp [Ot]
 · intro i
   fin_cases i <;> simp [Ot,bvb,bva]
private abbrev toOver (n:ℕ) :Raw n →+* Over n :=
 zDK (algebraMap FX aQ)
private theorem enX :
   (incl aQ).comp (toOver 2)=(toOver 3).comp pZ:= by
 apply zXT
 · intro a
   simp [pZ]
 · intro i
   simp [pZ]
private theorem enY:incl aQ (B4 0 1)=B4 0 1 := by
 simp [B4]
private theorem fXW :
   (Ot aQ).toRingEquiv.toRingHom.comp (toOver 3) =
     (zhd (toOver 2)).comp apf.toRingEquiv.toRingHom:= by
 apply zXT
 · intro a
   simp [Ot,apf]
 · intro i
   fin_cases i <;> simp [Ot,apf,bvb,bva,cfD]
private theorem efQ (C₀:sQ) [Fact (Irreducible C₀)]
   (hC:bbr C₀) (P:znc (y7 C₀)[X]) :
   (P.comap (LG C₀)).map (LG C₀)=P:= by
 let A:=aZ ⧸ BI C₀
 let T:=y7 C₀
 let:za6 A:=z0w (BI C₀)
 let:za6 A[X] :=zqU
 let φ:A →+* T:=bv8 C₀ hC.kernel
 let:zZE A T:=φ.toAlgebra
 let:z0o A T:=hC.localized
 let:zZE A[X] T[X] :=z88 A T
 let M:zdT A[X] :=(nonZeroDivisors A).map z1z
 let:zNo M T[X] :=zyz (nonZeroDivisors A) T
 let u:kM →+* A[X] :=
   (zhd (zVv (BI C₀))).comp
     apf.toRingEquiv.toRingHom
 have hu:zpX u :=
   (zMr _ zld).comp apf.surjective
 have hφ:φ.comp (zVv (BI C₀))=O4 C₀:=rfl
 have h:LG C₀=(algebraMap A[X] T[X]).comp u:= by
   rw [bqA,← hφ,← zPl]
   rfl
 rw [h,← zg6,← z0L,zNE _ hu]
 exact zvH M T[X] P
private theorem acI (C₀:sQ) [Fact (Irreducible C₀)]
  (hC:bbr C₀) (J:znc kM) (P:znc (y7 C₀)[X])
  (hJ:J=P.comap (LG C₀)) :
  (BI C₀).map pZ≤J:= by
 apply Ideal.map_le_iff_le_comap.mpr
 intro s hs
 have hzero :O4 C₀ s=0:=RingHom.mem_ker.mp (hC.kernel.symm ▸ hs)
 have hsC:apf.toRingEquiv.toRingHom (pZ s)=z1z s :=
  zmU cfB s
 have h:LG C₀ (pZ s)=0:= by
  rw [bqA,zQb,hsC]
  rw [zKC,zrL,hzero,map_zero]
 rw [hJ]
 change LG C₀ (pZ s)∈P
 rw [h]
 exact P.zero_mem
private def aoH (I:znc aZ) :Over 3 →ₐ[aQ] (SG I)[X] :=
 (Polynomial.mapAlgHom (zvR aQ (i9 I 0 1))).comp
   (Ot aQ).toAlgHom
private theorem eLI (I:znc aZ) :
   zpX (aoH I) :=
 (zMr _ zld).comp
   (Ot aQ).surjective
private theorem eLG (I:znc aZ) :
   zdq (aoH I).toRingHom =
     (i9 I 0 1).map (incl aQ) := by
 let e :=(Ot aQ).toRingEquiv
 change zdq ((zhd (zVv (i9 I 0 1))).comp
   e.toRingHom)= _
 rw [← zEW,zfT,zlC,
   ← fXT aQ,← z0L]
 exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
private def fXU (I:znc aZ) (J:znc kM)
   (hseed :I.map pZ≤J) :
   abX J ≃ₐ[aQ]
     ((SG I)[X] ⧸ (J.map (toOver 3)).map (aoH I).toRingHom) := by
 let W:=J.map (toOver 3)
 let f :=aoH I
 have hker :zdq f.toRingHom =
     (I.map pZ).map (toOver 3) ⊔ zye {B4 (0:Fin 3) 1} := by
   rw [eLG]
   change ((I.map (toOver 2) ⊔ zye {B4 (0:Fin 2) 1}).map (incl aQ))= _
   rw [Ideal.map_sup,z0L,enX,← z0L,zlN,
     zyk,enY]
 have hsmall: (I.map pZ).map (toOver 3)≤W :=
   Ideal.map_mono (f :=toOver 3) hseed
 have hsup:W ⊔ (I.map pZ).map (toOver 3)=W:=sup_eq_left.mpr hsmall
 have hW:W ⊔ zdq f.toRingHom=i9 J 0 1 := by
   rw [hker,← sup_assoc,hsup]
 let g:=(zvR aQ (W.map f.toRingHom)).comp f
 have hf :zpX f.toRingHom:=eLI I
 have hg:zpX g:=Ideal.Quotient.mk_surjective.comp hf
 have hgker :zdq g.toRingHom=i9 J 0 1 := by
   change zdq ((zVv (W.map f.toRingHom)).comp f.toRingHom)= _
   rw [← zEW,zlC,
     zEk f.toRingHom hf W,
     ← zPx,hW]
 exact (z9k aQ hgker.symm).trans
   (zEK hg)
private theorem eQE {T B:Type} [zrb T] [zrb B]
   (η:T →+* B) (P:znc T[X]) :
   zsE B (B[X] ⧸ P.map (zhd η)) =
     zsE T (T[X] ⧸ P) := by
 let:EuclideanDomain T[X] :=zaz
 let:IsPrincipalIdealRing T[X] :=EuclideanDomain.instIsPrincipalIdealRing
 let:P.IsPrincipal:=IsPrincipalIdealRing.principal P
 let p:=z1N P
 have hp:zye {p} = P:=zOZ P
 rw [← hp,zlN,zyk,finrank_quotient_span_eq_natDegree,
   finrank_quotient_span_eq_natDegree]
 exact zt8 η.injective p
private theorem gnM {F T B R:Type} [zrb F] [zrb T] [zrb B]
  [za6 R] [zZE F R] [zZE F B] (η:T →+* B) (P:znc T[X])
  (e :R ≃ₐ[F] (B[X] ⧸ P.map (zhd η))) :
  zsE F R=zsE F B*zsE T (T[X] ⧸ P) := by
 calc
  zsE F R=zsE F (B[X] ⧸ P.map (zhd η)) :=
    e.toLinearEquiv.finrank_eq
  _=zsE F B*zsE B (B[X] ⧸ P.map (zhd η)) :=
    (Module.finrank_mul_finrank F B _).symm
  _ = _:=congrArg (zsE F B * ·) (eQE η P)
theorem proof :aqd.c2 := by
 intro C₀ hC₀ J P hC _ hJ _ _
 let I:=BI C₀
 let A:=gk I
 let B:=SG I
 let T:=y7 C₀
 let:I.IsPrime :=show (BI C₀).IsPrime from
   hC.kernel ▸ zgL (O4 C₀)
 let:zrb B:=(eLP C₀ hC).toField
 let:za6 A:=z0w I
 let φ:A →+* T:=bv8 C₀ hC.kernel
 let b:A →+* B:=toSlice I 0 1
 let u:aZ →+* A:=zVv I
 let:zZE A T:=φ.toAlgebra
 let:z0o A T:=hC.localized
 have hb:zq4 b:=gBU I
 let η:T →+* B:=zIj (A:=A) (K:=T) (L:=B) (g:=b) hb
 have hηbase :η.comp φ=b:= by
   apply RingHom.ext
   intro x
   change η (algebraMap A T x)=b x
   exact zoc (A:=A) (K:=T) (L:=B) (g:=b) hb x
 have hφ:φ.comp u=O4 C₀:=rfl
 have hbu:b.comp u=(zVv (i9 I 0 1)).comp (toOver 2) :=rfl
 have hη:η.comp (O4 C₀)=(zVv (i9 I 0 1)).comp (toOver 2) := by
   rw [← hφ,← zxS,hηbase,hbu]
 have hcomp: (aoH I).toRingHom.comp (toOver 3) =
     (zhd η).comp (LG C₀) := by
   change (zhd (zVv (i9 I 0 1))).comp
     ((Ot aQ).toRingEquiv.toRingHom.comp (toOver 3))= _
   rw [fXW,bqA,← zxS,zPl,
     ← hη,← zPl,zxS]
 have hmap : (J.map (toOver 3)).map (aoH I).toRingHom =
     P.map (zhd η) := by
   rw [z0L,hcomp,← z0L,hJ,efQ C₀ hC]
 let e :=(fXU I J (acI C₀ hC J P hJ)).trans
   (z9k aQ hmap)
 exact gnM η P e
end
end bzY
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace cy7
noncomputable section
open cu gT pI OH
open GK (coord qw vV toSlice aEa)
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev AH :aZ →+* Ambient:=oi.comp pZ
private theorem co5 {I:znc Ambient} (hI:xN I) :
   zq4 ((zVv I).comp AH) := by
 let q:=(zVv (I.map Dk)).comp Dk
 let e :aQ →+* Y0 I:=algebraMap aQ (Y0 I)
 have he :q.comp AH=e.comp (algebraMap aZ aQ) := by
   apply zXT
   · intro c
     simp only [zQb]
     rw [← zKm,← zG3 FX aZ aQ]
     simp [q,oi,pZ,Dk]
     rfl
   · intro i
     fin_cases i <;> simp [q,AH,oi,pZ,Dk,e,ek] <;> rfl
 let:Nontrivial (Y0 I) :=zcE hI.seed_size.1
 apply (injective_iff_map_eq_zero ((zVv I).comp AH)).2
 intro f hf
 have hmem:AH f∈I:=Ideal.Quotient.eq_zero_iff_mem.mp hf
 have hz :q (AH f)=0 :=
   Ideal.Quotient.eq_zero_iff_mem.mpr (z7X Dk hmem)
 have hzero : (e.comp (algebraMap aZ aQ)) f=0:= by
   rw [← he]
   exact hz
 have hinj:zq4 (e.comp (algebraMap aZ aQ)) :=
   e.injective.comp (zxb aZ aQ)
 exact hinj (hzero.trans (map_zero (e.comp (algebraMap aZ aQ))).symm)
theorem eJ3 {I:znc Ambient} (hI:xN I) :
    zq4 (qw I 0 1) := by
  let u:aZ →+* aZ[X] :=
    zOD (Polynomial.C.comp znf)
      ![z7y,z1z (z9v 0)+Polynomial.X*z1z (z9v 1)]
  let v :aZ →+* FX[X] :=
    zOD z1z ![z7y,0]
  let e :=z8s FX 1
  let w:=MvPolynomial.uniqueAlgEquiv FX (Fin 1)
  have hv : (zhd v).comp u =
      (zhd w.toRingHom).comp e.toRingHom:= by
    apply zXT
    · intro a
      simp [u,v,e,w,zyf,zJG,
        zQb]
    · intro j
      fin_cases j
      · simp [u,e,zOO,zQb]
      · change zhd v (u (z9v 1)) =
          zhd w.toRingHom (e (z9v (0:Fin 1).succ))
        rw [show e (z9v (0:Fin 1).succ)=z1z (z9v (0:Fin 1)) from
          z07 (R:=FX) (j:=(0:Fin 1))]
        simp [u,v,w,zJG]
  have hu:zq4 u:= by
    apply z6j (f :=zhd v)
    change zq4 ((zhd v).comp u)
    rw [hv]
    exact (zTo w.toRingHom w.injective).comp e.injective
  let g:=(zVv I).comp AH
  have hg: (zhd g).comp u=qw I 0 1 := by
    apply zXT
    · intro a
      simp [g,u,qw,AH,oi,pZ,zQb]
      rfl
    · intro j
      fin_cases j <;>
        simp [g,u,qw,AH,oi,pZ,coord,zQb]
  rw [← hg]
  exact (zTo g (co5 hI)).comp hu
private abbrev Lg:=z3y (Fin 4) aZ
private abbrev Ek :zdT Lg :=
 aZ⁰.map (znf (σ:=Fin 4))
private def CV:Ambient →+* Lg:=zDK znf
private def blR:Lg :=
 z9v 0+MvPolynomial.C (z9v 0)*z9v 1 -
  znf (z9v 1)
private def wW (I:znc Ambient) :Lg →+* (gk I)[X] :=
 zOD (qw I 0 1) (fun i=>z1z (coord I i))
private theorem ax8 (I:znc Ambient) :
   (wW I).comp CV=Polynomial.C.comp (zVv I) := by
 apply zXT
 · intro a
   simp [wW,CV,qw]
   rfl
 · intro i
   simp [wW,CV,coord]
private theorem a1C (I:znc Ambient) :zpX (wW I) := by
  let u:=zqf CV
    (znf (z9v 0) :Lg)
  have he : (wW I).comp u=zhd (zVv I) := by
    apply z86
    · intro a
      simp only [zQb,u,z4Q,zJU,
        zKC,zrL]
      exact zLs (ax8 I) a
    · simp [u,wW,qw]
  have hs :zpX ((wW I).comp u) := by
    rw [he]
    exact zMr _ zld
  exact Function.Surjective.of_comp (f :=wW I) (g:=u) hs
private theorem bfm :
   (algebraMap Lg N8).comp CV= Q6:= by
 change (zDK (algebraMap aZ aQ)).comp CV= Q6
 apply zXT
 · intro a
   simp only [zQb,CV,Q6,zpw]
   rfl
 · intro i
   simp only [zQb,CV,Q6,z7N]
private theorem exV :
  algebraMap Lg N8 blR=B4 0 1 := by
 change zDK (algebraMap aZ aQ) blR=B4 0 1
 simp only [blR,map_add,map_mul,map_sub,z7N,zpw,
  B4,ek]
private theorem b19 (I:znc Ambient) :
    (zVv (Cr I)).comp (algebraMap Lg N8) =
      (vV I 0 1).comp (wW I) := by
  change (zVv (Cr I)).comp (zDK (algebraMap aZ aQ))= _
  apply zXT
  · intro a
    change zVv (Cr I)
        (zDK (algebraMap aZ aQ) (znf a)) =
      vV I 0 1 (wW I (znf a))
    rw [zpw,wW,zTv]
    have h:=(zLs (aEa I 0 1) a).symm
    change zVv (GK.i9 I 0 1)
        (znf (algebraMap aZ aQ a)) =
      vV I 0 1 (qw I 0 1 a) at h
    change zVv (GK.i9 I 0 1)
        (znf (algebraMap aZ aQ a)) =
      vV I 0 1 (qw I 0 1 a)
    exact h
  · intro i
    change zVv (Cr I)
        (zDK (algebraMap aZ aQ) (z9v i)) =
      vV I 0 1 (wW I (z9v i))
    rw [z7N,wW,zrD,vV,
      z4Q,zJU,toSlice,coord,z5h,
      z7N]
    rfl
abbrev aXs (I:znc Ambient) :
   zZE ((gk I)[X]) (rM I) :=
 (vV I 0 1).toAlgebra
abbrev bwa (I:znc Ambient) :zdT ((gk I)[X]) :=
 aZ⁰.map (qw I 0 1)
theorem cYE (I:znc Ambient) :
    letI:zZE ((gk I)[X]) (rM I) :=aXs I
    zNo (bwa I) (rM I) := by
  let:zZE ((gk I)[X]) (rM I) :=aXs I
  have hden:Ek.map (wW I)=bwa I:= by
    change (aZ⁰.map (znf (σ:=Fin 4)).toMonoidHom).map
      (wW I).toMonoidHom=aZ⁰.map (qw I 0 1).toMonoidHom
    rw [Submonoid.map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    exact zTv _ _ _
  rw [← hden]
  apply IsLocalization.of_surjective (S' := rM I) Ek N8
    (wW I) (a1C I) (zVv (Cr I))
    zld (b19 I)
  rw [zlC,Cr]
  apply sup_le
  · rw [← bfm,← z0L]
    apply Ideal.map_mono
    rw [zo0]
    intro a ha
    change wW I (CV a)=0
    rw [show wW I (CV a)=z1z (zVv I a)
        from zLs (ax8 I) a,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha,map_zero]
  · rw [← exV,zvl]
    apply z7X
    change wW I blR=0
    simp [wW,blR,qw]
private theorem aSS (k A:Type) [zrb k] [za6 A] [ztn A]
    [zZE k A] [zUK k A] :
    ∃ d:ℕ,ringKrullDim A=(d:WithBot ℕ∞)∧zls k A=(d:Cardinal) := by
  obtain ⟨d,g,hg,hfin⟩:=exists_finite_inj_algHom_of_fg k A
  let R:=z3y (Fin d) k
  let:zZE R A:=g.toRingHom.toAlgebra
  let:zAa R A:=hfin
  let:zVK R A:=Algebra.IsIntegral.of_finite R A
  let:FaithfulSMul R A:=(faithfulSMul_iff_algebraMap_injective R A).mpr hg
  let:zsf k R A:=IsScalarTower.of_algHom g
  have hdim:ringKrullDim R=(d:WithBot ℕ∞) := by
    simp [R,zmx,ringKrullDim_eq_zero_of_field]
  refine ⟨d,?_,?_⟩
  · rw [← hdim]
    apply le_antisymm
    · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
      intro a b hab
      exact zu8 (R:=R) (show a.asIdeal<b.asIdeal from hab)
    · rw [hdim]
      obtain ⟨l,hl⟩:=Order.le_krullDim_iff.mp hdim.ge
      let:l.head.asIdeal.IsPrime :=l.head.isPrime
      have hbot: (⊥ : znc A).under R≤l.head.asIdeal:= by
        change Ideal.comap (algebraMap R A) ⊥ ≤ l.head.asIdeal
        rw [← zPx,(zli _).mp
          (FaithfulSMul.algebraMap_injective R A)]
        exact bot_le
      obtain ⟨P,_,hP,hhead⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : znc A) hbot
      let:P.IsPrime :=hP
      let:P.LiesOver l.head.asIdeal:=⟨hhead.symm⟩
      obtain ⟨L,hL,_,_⟩:=z1m l P
      exact Order.le_krullDim_iff.mpr ⟨L,hL.trans hl⟩
  · let:zjH R A:=Algebra.IsAlgebraic.of_finite R A
    simpa [R,trdeg_eq_zero (R:=R) (A:=A),Cardinal.mk_fin] using
      (trdeg_add_eq (A:=A) k R).symm
private theorem cua :zls FX aQ=2 := by
 let:zjH aZ aQ:=zyQ aQ aZ⁰
 simpa [aZ,trdeg_eq_zero (R:=aZ) (A:=aQ),Cardinal.mk_fin] using
  (trdeg_add_eq (A:=aQ) FX aZ).symm
private theorem c7V {I:znc Ambient} [I.IsPrime] (hI:xN I) :
  bwa I≤(gk I)[X]⁰ :=
 map_le_nonZeroDivisors_of_injective (qw I 0 1) (eJ3 hI) le_rfl
private theorem gpd {I:znc Ambient} [I.IsPrime] (hI:xN I) :
  ztn (rM I) := by
 let:zZE ((gk I)[X]) (rM I) :=aXs I
 let:zNo (bwa I) (rM I) :=cYE I
 exact IsLocalization.isDomain_of_le_nonZeroDivisors (rM I) (c7V hI)
private theorem gnG (I:znc Ambient) (a :FX) :
   algebraMap FX (rM I) a =
     vV I 0 1 (algebraMap FX (gk I)[X] a) := by
 change zVv (Cr I) (znf (algebraMap FX aQ a)) =
   vV I 0 1 (z1z (zVv I (znf a)))
 rw [vV,z4Q,zJU,toSlice,
   z5h,zpw]
 rfl
private theorem ct6 (k R S:Type) [zrb k] [za6 R] [za6 S]
  [ztn R] [ztn S] [zZE k R] [zZE k S] [hAlg:zZE R S]
  [FaithfulSMul k R] (M:zdT R) [hLoc:zNo M S]
  (hM:M≤R⁰)
  (hcomp : ∀ x :k,algebraMap k S x=algebraMap R S (algebraMap k R x)) :
  zls k S=zls k R:= by
 let:zsf k R S:=zsL hcomp
 let:FaithfulSMul R S:=(faithfulSMul_iff_algebraMap_injective R S).mpr
  (IsLocalization.injective S hM)
 let:zjH R S:=zyQ S M
 simpa only [trdeg_eq_zero (R:=R) (A:=S),add_zero] using
  (trdeg_add_eq (A:=S) k R).symm
private theorem ct8 (k R:Type) [zrb k] [za6 R] [ztn R]
  [zZE k R] [FaithfulSMul k R] :
  zls k R[X]=zls k R+1 := by
 let:FaithfulSMul R R[X] :=(faithfulSMul_iff_algebraMap_injective R R[X]).mpr
  zmy
 simpa only [zBA] using (trdeg_add_eq (A:=R[X]) k R).symm
private theorem ct9 {I:znc Ambient} [I.IsPrime]
  [ztn (rM I)] (hI:xN I) :
  zls FX (rM I)=zls FX (gk I)+1 := by
 let R:=gk I
 let S:=rM I
 let:FaithfulSMul FX R :=
  (faithfulSMul_iff_algebraMap_injective FX R).mpr (algebraMap FX R).injective
 let:FaithfulSMul FX R[X] :=
  (faithfulSMul_iff_algebraMap_injective FX R[X]).mpr (algebraMap FX R[X]).injective
 have hloc:=ct6 FX R[X] S (hAlg:=aXs I)
  (bwa I) (hLoc:=cYE I)
  (c7V hI) (gnG I)
 exact hloc.trans (ct8 FX R)
theorem proof :OH.c1 := by
 intro I hI
 let S:=rM I
 let:I.IsPrime :=hI.prime
 let:ztn S:=gpd hI
 refine ⟨?_,?_⟩
 · intro htop
   have hsub:Subsingleton S:=Ideal.Quotient.subsingleton_iff.mpr htop
   exact zero_ne_one (hsub.elim (0:S) 1)
 obtain ⟨d,hd,ht⟩:=aSS FX (gk I)
 have hd' : d = 2 := by
   rw [hI.dimension] at hd
   exact_mod_cast hd.symm
 have htotal:zls FX S=3:= by
   rw [ct9 hI,ht,hd']
   norm_num
 let:FaithfulSMul aQ S :=
   (faithfulSMul_iff_algebraMap_injective aQ S).mpr (algebraMap aQ S).injective
 have htower :=trdeg_add_eq (A:=S) FX aQ
 rw [cua,htotal] at htower
 have hrel :zls aQ S=1 := by
   apply Cardinal.eq_of_add_eq_add_left (a :=2)
   · exact htower.trans (by norm_num)
   · simp
 obtain ⟨e,he,hte⟩:=aSS aQ S
 have he' : e=1 := by
   rw [hrel] at hte
   exact_mod_cast hte.symm
 simpa [he'] using he
end
end cy7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GK
noncomputable section
open K1 cu gT YY
open scoped Polynomial
private theorem bND (I:znc Ambient) [I.IsPrime] [Nontrivial (rM I)]
   [zAa aQ (rM I)] :xg I ≠ ⊥ := by
 have hf :=Module.Finite.of_injective (aWo I).toLinearMap (c4d I)
 intro h
 rw [h] at hf
 let e :=bfg (⊥ : znc aZ)
 have he : (⊥ : znc aZ).map ajM = ⊥ := Ideal.map_bot
 have e' : SG (⊥ : znc aZ) ≃ₐ[aQ]
     (aQ[X] ⧸ (⊥ : znc aQ[X])) :=he ▸ e
 exact Polynomial.not_finite
   (Module.Finite.equiv (e'.trans (AlgEquiv.quotientBot aQ aQ[X])).toLinearEquiv)
private theorem gog (I:znc Ambient) [Nontrivial (rM I)] :
   ¬ (xg I).IsMaximal:= by
 intro hM
 let P:=xg I
 let B:=gk P
 let:P.IsMaximal:=hM
 let:zrb B:=Ideal.Quotient.field P
 let:zAa FX B:=finite_of_finite_type_of_isJacobsonRing FX B
 let f :aZ →ₐ[FX] B[X] :=
   ⟨qw P 0 1,by
     intro a
     change qw P 0 1 (znf a)=z1z (algebraMap FX B a)
     simp [qw]
     rfl⟩
 have hdim:=trdeg_le_of_injective f (eLY I)
 rw [zUx,← trdeg_add_eq FX B (A:=B[X]),
   trdeg_eq_zero (R:=FX) (A:=B),zBA,zero_add] at hdim
 have hbad: (2 :Cardinal.{0})≤1 := by
   simpa only [Cardinal.lift_id,Cardinal.mk_fin,Nat.cast_ofNat] using hdim
 have hn: (2 :ℕ)≤1 := by exact_mod_cast hbad
 omega
private theorem gof (I:znc Ambient) [I.IsPrime] [Nontrivial (rM I)]
  [zAa aQ (rM I)] : (xg I).height = 1 := by
 let P:=xg I
 let:P.IsPrime :=bg7 I
 have hP0: (⊥ : znc aZ)<P:=bot_lt_iff_ne_bot.mpr (bND I)
 have hlo:1≤P.height:= by
  simpa using zSK hP0
 obtain ⟨M,hM,hPM⟩:=P.exists_le_maximal (zns ‹P.IsPrime›)
 let:M.IsPrime :=hM.isPrime
 have hlt:P<M:=lt_of_le_of_ne hPM (by
  intro h
  have hmax :P.IsMaximal:= by rw [h]; exact hM
  exact gog I hmax)
 have hdim:ringKrullDim aZ=2 := by
  rw [zmx,ringKrullDim_eq_zero_of_field]
  norm_num [zey]
 have hhi:M.height≤2 := by
  have h:=ztp (I:=M)
  rw [hdim] at h
  exact WithBot.coe_le_coe.mp h
 have hP:=(zSK hlt).trans hhi
 have hle :P.height≤1 :=
  (ENat.add_le_add_iff_right (by simp : (1 :ℕ∞) ≠ ⊤)).mp hP
 exact hle.antisymm hlo
theorem proof :YY.c1 := by
  intro I h
  let:I.IsPrime :=h.1
  let:zAa aQ (rM I) :=h.2.2.1
  let:Nontrivial (rM I) :=zcE h.2.2.2
  let P:=xg I
  let:P.IsPrime :=bg7 I
  have :UniqueFactorizationMonoid FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  have :UniqueFactorizationMonoid aZ:=zhK (Fin 2)
  obtain ⟨F,hmem,hprime⟩:=zUo
    (bg7 I) (bND I)
  have hspan:P=zye {F} :=
    zRh (gof I) hmem hprime
  refine ⟨F,hprime.irreducible,hspan,?_,?_⟩
  · by_contra! hz
    have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (za7 hz)
    have hc:F.coeff 0≠0:= by
      intro h0
      exact hprime.ne_zero (by simpa [h0] using he)
    exact hprime.not_isUnit (he ▸ hc.isUnit.map znf)
  · have hbound:=zdv
      (f :=(aWo I).toLinearMap) (c4d I)
    have hd:zsE aQ (SG P)=F.totalDegree := by
      rw [(bfg P).toLinearEquiv.finrank_eq,hspan,zlN,zyk,
        finrank_quotient_span_eq_natDegree,bO8]
    exact hd ▸ hbound
end
end GK
end
section
namespace aR0
open pI
theorem proof :ac2.c2 := by
 intro I hI hd
 obtain ⟨g,hg,hIg⟩:=eN5 hI hd
 exact ⟨g,hg,(dVu hI g hg.ne_zero hIg).trans_lt hI.mixed_lt,hIg⟩
end aR0
end
section
set_option maxHeartbeats 0
set_option maxRecDepth 50000
namespace acY
open acY.Compact
private def p0:Chunk 3103 4 353762352 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68102364ac8495d2b28ad78a816a26fcccae127e62cbab8156e69ed19e9368e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66102d646c959092665651eaf1502e14dfa135be4fcd4a11702adcd3da34487afc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc7648d9d737a574aca2b63a905c2bc7332b85909a92eae057bda199e870f2a95028214942a13a993291281922891811128108090002786ad96831703af07b19a0b591b2564249995947ac7520b8352e6fcccae127e62cbab8156e69e679f737 (by decide +kernel) (by decide +kernel)
private def p4 :Chunk 3107 4 361029740 :=
 cert _ _ _ 0x2715028214942693a6132592819225118111249080900005ad2c968317038731331a041a88d92b2124ccf5a2b5de90da9a95426be49f9a9422f355c9a79a67c4de38f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841a8b591b25642499959456bc540b5337e6656f9ef3165d5e6ab934f345161f3f1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f6433083511b256424ae959456bc540b5137e6657093f352845e6ab934f345109ed52a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340816b2364ac849332b28f578a416a26fd09adf27e6a4babcd56e69e689f437 (by decide +kernel) (by decide +kernel)
private def p8:Chunk 3111 4 369479195 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106ab4a46c959092667ad49aef486e1d4a9995f27bcc597550669e6a9f1378e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106cb4a75cde95d2b28ad77a436aaa54ccadf5f24fcd4a1179aae4d3cd54587cfc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d846c959092667ad15aef502d554aa135f24fcd497557269e6aa163caa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a0c5c0ebc1ec668106a2d675cde95d2b28ad78a816a66fcccadf3de62cbabcd57269e699f137 (by decide +kernel) (by decide +kernel)
private def zF:Chunk 3115 4 377063046 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a123ae6f4ae959456bb54db5733251c9f9a9422a0cd3c373b06b1c7c14111879147510706d0c686508600c5c59045408504d00480444002c355cb018bc1c383d94cc20d8244ac849333d6a4d77a436ae664a393f3528450398f86e820edf8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b2d291b25642499959456bbd21b8752a6657c9ef3165d5419a7b4e884f6a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848959092ba56515aef486d554a99928e4fcd4a1150669ed39e336 (by decide +kernel) (by decide +kernel)
private def TF:Chunk 3119 4 385707450 :=
 cert _ _ _ 0x2715028214942693a6132592819225118111249080900005ad2c968317038731331a041a84a6d9092ba56549aed536cc58ba1528e7bcc5ae736263e6c9e3368e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c12b524ac849333d6a4d76a9b6b2caca39ef316845039a79ae84cf1f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b04ad492b37a574aca2b5daa6dabb2b42a51c9f9a942281cc7cd743c7b54a81410a4a1509d4c9948940c91448c088940840480013c356cb418b81d783d8cd020d4256a4959092667ad49aef486d5d4ab2b28e7bcc5a1140e69e1b9ee37 (by decide +kernel) (by decide +kernel)
private def WU:Chunk 3123 4 394945159 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a12142124ccf5a93636a7598b1742a9a49f98b5ce6c4d3cdd3c06d1c7c14111879147510706d0c686508600c5c59045408504d00480444002c355cb018bc1c383d94cc20d82536c959bd2ba7ad49b1b53acc58ba1528e4fcd4ae736263e6ea1e3d7e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c129b6424999eb526bb54db3162e854a39ef316b9cd89a79b284cf2a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a84a6d92b2124ccf5a935daa6dacb2b4d24fcd4ae740e69e6c9e336 (by decide +kernel) (by decide +kernel)
private def p24 :Chunk 3127 4 403356299 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a12149be424999eb526e249a99128e4fcd4b1529663ed59d5358e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c12149be6f4ae9eb636a749a99128e7bcc5b1529669e1ca053b7e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c12142124ccf5a93636a749aa154d24fcd4b1529663e1ca053baa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a0c5c0ebc1ec668106a12149be6f4ae9eb5daa6c9a99128e7bcc5ae736263e1c9d535 (by decide +kernel) (by decide +kernel)
private def p28:Chunk 3131 4 412543934 :=
 cert _ _ _ 0x138a81410a4a1349d30992c940c91288c088924840480002d6964b418b81c398998d020d424296b4de95d2b2f3dc4935302644a39ef316c54a59a7876780da38f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b04852d69bd2667ade7b8926a604c894727e6a558c3d29663e1da1b3d7e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c12149be6f4ae95979ec6d4e935302644a39ef316c54a598f87686cf6a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a84852d69bd2667ade7b1b53a4d4c0a154d24fcc5b1529669ed59eb37 (by decide +kernel) (by decide +kernel)
private def p32 :Chunk 3135 4 421558539 :=
 cert _ _ _ 0x2715028214942693a6132592819225118111249080900005ad2c968317038731331a041a848506099959666e249a9b9302644a393f352b961f94b31f6c4f41bc71f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a5af37a4ccacb3353a4d4dc98132251cf798b5630f4a598fb62898f9f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b04852d795d666e249ace342a9a49f98b5630f4a59a79c2814eea95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a84852d79bd26656599b8926a604c894727e6a558c3d29663e709eb37 (by decide +kernel) (by decide +kernel)
private def p36:Chunk 3139 4 430917656 :=
 cert _ _ _ 0x138a81410a4a1349d30992c940c91288c088924840480002d6964b418b81c398998d020d424283180499f829d26aa7cdc98132251cf798b5cb0fca598f9ca7c0e238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b0485060aef829d26a884dc98142a9a49f98b5630fca598f882854f5f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b048506099f838926a6e4c099128e4fcd4ae587e52cc7c414147954a81410a4a1509d4c9948940c91448c088940840480013c356cb418b81d783d8cd020d4242830577c14e935372604c89473de62d58c3d29663e209da36 (by decide +kernel) (by decide +kernel)
private def p40:Chunk 3143 4 441011209 :=
 cert _ _ _ 0x138a81410a4a1349d30992c940c91288c088924840480002d6964b418b81c398998d020d4242831b5065c590d5364d5c6a213726050aa6927e62d72c4329663e73a063a8e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c121418da832e2fc14e93553e6e4c099128e4fcd4b1188652cc7ce74507efc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d82428318060cb8bf053a4d5c6a219c6854a39ef316b961f94b31f39d159fd52a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c6d419717e0a749aa21372604c894727e6a588c4329663e729f839 (by decide +kernel) (by decide +kernel)
private def p44 :Chunk 3147 4 450490395 :=
 cert _ _ _ 0x4e2a050429284d274c264b2503244a23022249210120000b5a592d062e070e6266340835090a0c1014f21a90cfbafb53e6e4c099128e4fcd491d29663e759f0388e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c1214182029fe0a6c9aafb71a88671a154d24fcc5b1123a6c4c7ceb4507efc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b453c86a9b26b6cd109b9302644a393f352c462194b31f3a5159fd52a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c1014ff05364d57da9f372604c89473de62d88c4329663e749f839 (by decide +kernel) (by decide +kernel)
private def p48:Chunk 3151 4 460183825 :=
 cert _ _ _ 0x2715028214942693a6132592819225118111249080900005ad2c968317038731331a041a8485060837086a4326aaedc6a219c68553493f3165b4a59c79de7b4e238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b048506080a790d5364d55da21372604c894727e6a48e94b31f3b5101f3f1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f64330836090a0c6d6e10d4864d55da9f372604c89473de62c8e94b31f3b50e9f552a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c106e7829b26abeed9a213726050aa6927e62d8891d29671e76a003a (by decide +kernel) (by decide +kernel)
private def p52 :Chunk 3155 4 469938859 :=
 cert _ _ _ 0x2715028214942693a6132592819225118111249080900005ad2c968317038731331a041a848506080daee10d4864d55ea21372604c894727e62cb694b38f11cfc1cc71f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c106e10d4864d55ea9f372604c89473dead62296d36263edaa283f7e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c121418da36bb8435219355776cd109b9302644a393f3165b4a59c7b6a8cd02a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848506080da94f21a90cfbabb53e6e4c099128e4fcd491d29663e779fb39 (by decide +kernel) (by decide +kernel)
private def p56:Chunk 3159 3 359161995 :=
 cert _ _ _ 0x238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b048506080daee10d4864d57ea21372604c894727ead62296d29671e78a33407e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c121418dad8dcf03baa04fbabd53e6e4c099128e4fcc5c4523a52cc7c474708354a81410a4a1509d4c9948940c91448c088940840480013c356cb418b81d783d8cd020d4242830406d77086a4326aaf5c6a213726050aa6927ead62296d29671e23a0e3b (by decide +kernel) (by decide +kernel)
private def c:Chunk 3103 59 6091149653 :=
 add p0 <| add p4 <| add p8 <| add zF <| add TF <| add WU <| add p24 <| add p28 <| add p32 <| add p36 <| add p40 <| add p44 <| add p48 <| add p52 <| p56
end acY
end
section
namespace wH
noncomputable section
open Polynomial K1 aR
theorem cY3:zq4 Ud:= by
 intro S T h
 have h₀:=congrFun h (0:Fin 3)
 have hcoeff :zq4 qY :=
  (algebraMap iP cH).injective.comp
    (zxb ao[X] iP)
 exact hcoeff (by simpa [Ud,jet,Polynomial.hasseDeriv_zero'] using h₀)
end
end wH
end
section
namespace Tx
noncomputable section
open Polynomial K1 aR wH
abbrev gQ:=z3y (Fin 4) cH
abbrev oe :=Fin 4→cH
def zq (S:ao[X]) :oe := fun i=>qY (jet S i)
def Ol (y :oe) :znc gQ:=zdq (zY9 y)
def ay7 (f :af 4) :gQ:=zDK qY f
def vY (P:af 3) :gQ:=zHw Fin.castSucc (fW P)
def xJ (f :af 4) (P Q:af 3) :znc gQ :=
 zye {ay7 f,vY P,vY Q}
def ajK (r :PrimeSpectrum gQ) (J:znc gQ) :ℕ∞ :=
 let A:=Localization.AtPrime r.asIdeal
 Module.length A (A ⧸ J.map (algebraMap gQ A))
def Supported (H :Shape) (F:gQ) :Prop :=
  ∀ m∈F.support,m.sum (fun _ a=>a)≤H.b ∧
    m.sum (fun i a=>i.val*a)≤H.j∧m 3≤H.t
abbrev constantCoeff :K →+* cH :=qY.comp (Polynomial.C.comp embed)
structure a1h (H :Shape) where
 denominator :gQ
 numerator :I→ gQ
 denominator_supported:Supported H denominator
 numerator_supported : ∀ i,Supported H (numerator i)
def a1h.ar5 {H :Shape} (C:a1h H) (S:K[X]) :Prop :=
  let ev :=zY9 (zq (extend S))
  ev C.denominator≠0 ∧
    ∀ i,ev (C.numerator i)=constantCoeff (S.eval (node i))*ev C.denominator
end
end Tx
end
section
namespace K1_13_7_6
noncomputable section
open aR wH MvPolynomial
open scoped Pointwise
theorem dHY {σ:Type} [Finite σ]
  (φ:z3y σ cH →ₐ[cH] Lower) (hφ:zpX φ)
  (y :Sz) (q:PrimeSpectrum Lower) (hq:q.asIdeal=oF y) :
  aGW φ q=1 := by
 let ψ:z3y σ cH →ₐ[cH] cH :=(aeval y).comp φ
 have hψ:zpX ψ:= by
  intro t
  obtain ⟨v,hv⟩:=hφ (C t)
  exact ⟨v,by simp [ψ,hv]⟩
 have hker :q.asIdeal.comap φ=zdq ψ:= by
  rw [hq]
  rfl
 rw [aGW,hker]
 let e :=zEK hψ
 let:=Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
 rw [affineDegree_eq_finrank,e.toLinearEquiv.finrank_eq,Module.finrank_self,Nat.cast_one]
end
end K1_13_7_6
end
