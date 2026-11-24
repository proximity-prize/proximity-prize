import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.G
import ProximityPrize.SubmissionLower.H
import ProximityPrize.SubmissionLower.I
set_option Elab.async false
open _root_ renaming AdjoinRoot.mk → zY7, AlgHom.coe_toRingHom → zlv, AlgHom.commutes → zKk, AlgHom.toRingHom_eq_coe → ziQ, Algebra → zZE, Algebra.IsIntegral.isIntegral → zmn, Algebra.algebraMap → z12, Algebra.smul_def → zd5, AlgebraicIndependent → zlL, CharP.cast_eq_zero_iff → zX2, CommRing → za6, DFunLike.congr_fun → zmU, Derivation → zvY, Equiv.swap → zFe, Field → zrb, Fin.castLE → zQY, Fin.rev → z8T, Fin.rev_injective → zhY, Finset → zJe, Finset.le_sup → zZi, Finset.mul_sum → zxw, Finset.range → z4x, Finset.single_le_sum → zfK, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Finset.sum_eq_single_of_mem → zpa, Finset.sup_mono → zRS, Finsupp.prod_fintype → z6B, Finsupp.single → zhf, Finsupp.sum_fintype → z9d, Fintype.card → zhP, Function.Injective → zq4, Function.Semiconj → zEB, Function.Surjective → zpX, Function.comp_apply → z3s, Function.iterate_succ_apply' → zLk, Function.iterate_zero_apply → z56, Ideal → znc, Ideal.Quotient.commRing → z0w, Ideal.Quotient.lift → zP2, Ideal.Quotient.liftₐ → zTA, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.comap_map_of_bijective → zFA, Ideal.height → zmO, Ideal.map_map → z0L
open _root_ renaming Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton → zxV, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.span → zye, Ideal.subset_span → zCn, Irreducible → z5o, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsLocalization.Away.invSelf → zdx, IsLocalization.Away.lift → ztx, IsLocalization.Away.lift_eq → zaz, IsLocalization.isPrime_of_isPrime_disjoint → znL, IsLocalization.lift → zvq, IsLocalization.lift_eq → zX4, IsLocalization.map_units → z0j, IsLocalization.ringHom_ext → zuW, IsLocalization.under_map_of_isPrime_disjoint → ztT, IsRelPrime → zRK, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.algebraMap_eq → zYY, IsScalarTower.toAlgHom → zE2, IsSeparable → zR6, IsUnit → zWB, LinearIndependent → z14, LinearMap.congr_fun → z5U, LinearMap.smul_apply → zqa, Localization.Away → zUF, Module.Finite → zAa, Module.finrank → zsE, Module.finrank_eq_zero_of_subsingleton → z6g, Module.rank → z1x, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.affineDegree → zHf, MvPolynomial.affineDegree_nonneg → zcN, MvPolynomial.affineHilbertPolynomial → zIU, MvPolynomial.algHom_C → zWj, MvPolynomial.algebraMap_def → zu8, MvPolynomial.algebraMap_eq → zKm, MvPolynomial.coeff_mul_X' → z0S, MvPolynomial.coeff_pderiv → zcl, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X
open _root_ renaming MvPolynomial.eval_X → zV6, MvPolynomial.eval_map → znM, MvPolynomial.eval₂ → zSZ, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.eval₂_comp → z6r, MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus → zwb, MvPolynomial.finSuccEquiv → z8s, MvPolynomial.finSuccEquiv_X_succ → z07, MvPolynomial.finSuccEquiv_X_zero → zOO, MvPolynomial.finSuccEquiv_apply → zyf, MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree → z1b, MvPolynomial.hom_eval₂ → zUe, MvPolynomial.homogeneousComponent → zyc, MvPolynomial.induction_on → z5i, MvPolynomial.map → zDK, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.mem_support_iff → zuk, MvPolynomial.pderiv → zWe, MvPolynomial.pderiv_X → zYE, MvPolynomial.pderiv_X_of_ne → zVY, MvPolynomial.pderiv_mul → zGW, MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one → zdH, MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime → zAy, MvPolynomial.principalCut_sum_affineDegree_retainedMinimalPrimes_le → zcE, MvPolynomial.quotientDegreeLE → z9e, MvPolynomial.rename → zHw, MvPolynomial.renameEquiv → zGY, MvPolynomial.rename_X → z6l, MvPolynomial.ringHom_ext → zXT, MvPolynomial.sumAlgEquiv → z3k, MvPolynomial.support_map_subset → z88, MvPolynomial.uniqueAlgEquiv → zpe, MvPolynomial.zeroLocus → zSD, Nat.cast_mul → z2R, Nat.cast_succ → zg0, Nat.eq_zero_of_le_zero → za7, Nat.exists_eq_succ_of_ne_zero → zwS, Nat.factorial_succ → zwO, Nat.le_add_right → z8K, Nat.le_of_dvd → zTm, Nat.le_of_not_lt → z9m, Nat.lt_of_succ_lt → zws, Nat.mul_zero → zvM, Nat.strong_induction_on → z0n, Nat.sub_add_cancel → zxt
open _root_ renaming Nat.succ_pos → ztH, Nat.zero_add → zbc, Nat.zero_le → zD0, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.aeval → zEU, Polynomial.aeval_X → zw0, Polynomial.algebraMap_eq → zrE, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.coe_mapRingHom → zKC, Polynomial.coeff_derivative → zMD, Polynomial.coeff_eq_zero_of_natDegree_lt → zQl, Polynomial.coeff_zero → zO6, Polynomial.commRing → zqU, Polynomial.derivative → zst, Polynomial.derivative_C → zJH, Polynomial.derivative_X → zBT, Polynomial.derivative_mul → zAg, Polynomial.evalRingHom → zhy, Polynomial.eval_map → zhI, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_C → zJU, Polynomial.eval₂_C_X → z8i, Polynomial.eval₂_map → zem, Polynomial.factorial_smul_hasseDeriv → z6T, Polynomial.finsetSum_coeff → zaW, Polynomial.hasseDeriv → z75, Polynomial.hasseDeriv_map → zvb, Polynomial.hom_eval₂ → zly, Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity → zz7, Polynomial.le_natDegree_of_ne_zero → zZI, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.map_injective → zTo, Polynomial.natDegree_C_mul_le → zRn, Polynomial.natDegree_le_of_dvd → zkM, Polynomial.natDegree_lt_iff_degree_lt → z2f, Polynomial.natDegree_mul_le_of_le → zJZ, Polynomial.natDegree_pow_le_of_le → zxc, Polynomial.natDegree_sum_le_of_forall_le → zMZ, Polynomial.natDegree_taylor → zQU, Polynomial.ringHom_ext → z86, Polynomial.ringHom_ext' → z3l, Polynomial.taylor → zcJ, Polynomial.taylor_coeff → zWQ, Polynomial.taylor_coeff_zero → zPh
open _root_ renaming PrimeSpectrum → zy6, RingHom.comap_ker → zEW, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.ext → zz4, RingHom.id → zz5, RingHom.ker → zdq, RingHom.ker_comp_of_injective → zGm, RingHom.mem_ker → zry, Set.image_singleton → zyk, Set.mem_singleton → zT1, Set.ncard_coe_finset → zik, Set.ncard_le_ncard → zDB, Submodule → zpI, Submodule.mem_map_of_mem → zip, TrivSqZeroExt.ext → zMz, TrivSqZeroExt.fstHom → zx5, TrivSqZeroExt.inl → zx4, UniqueFactorizationMonoid → zsh, add_comm → zV7, add_zero → z0a, charP_of_injective_ringHom → zgG, congrArg → zPw, cu.Equation → zS3, dN.separant → zai, gT.Ambient → z87, gT.ek → z9Y, injective_iff_map_eq_zero → zLn, ite_eq_left → zYo, ite_eq_right → zNB, le_antisymm → zWs, le_sup_left → zPQ, left_ne_zero_of_mul → z67, map_add → zrl, map_dvd → ztu, map_eq_zero_iff → zVB, map_mul → zok, map_natCast → zGu, map_ne_zero_iff → zw1, map_pow → zkq, map_sub → zpO, map_sum → zdo, map_zero → zhc, mul_assoc → ztg, mul_comm → zDE, mul_div_cancel_left₀ → zE5, mul_one → zqe
open _root_ renaming nonZeroDivisors → zgt, nonZeroDivisors.ne_zero → zyw, not_le_of_gt → ziF, nsmul_eq_mul → zVT, pow_ne_zero → zm1, pow_zero → zJx, smul_eq_mul → zs5, wH.Lower → zza
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2500
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace czv
noncomputable section
open cu gT Cu aqd UI aiN
open scoped Polynomial
private abbrev aRw:=z3y (Fin 3) aQ
private abbrev baseChange :kM →+* aRw :=
 zDK (z12 FX aQ)
private abbrev TY (J:znc kM) :znc aRw :=
 J.map baseChange ⊔ zye {Pp 2}
private def aL8 (J:znc kM) :kM →+* SI J :=
 (zVv (TY J)).comp baseChange
private theorem ds4 (J:znc kM) :
   aL8 J (z9v 2)=z12 aQ (SI J)
     (z9Y 1) := by
 change zVv (TY J) (baseChange (z9v 2)) =
   zVv (TY J) (znf (z9Y 1))
 rw [z7N,Ideal.Quotient.mk_eq_mk_iff_sub_mem]
 exact (le_sup_right:zye {Pp 2} ≤ TY J)
   (z5J (Pp 2))
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem dLu (J:znc kM)
    (d:kM ⧸ J →+* SI J)
    (hd:d.comp (zVv J)=aL8 J)
    (q:SI J) :
    ∃ u:SI J,zWB u ∧ ∃ p: (kM ⧸ J)[X],
      q*u=zqf d
        (z12 aQ (SI J) (z9Y 0)) p:= by
  let D:=kM ⧸ J
  let Q:=SI J
  let:za6 D:=z0w J
  let:za6 D[X] :=zqU
  let mkQ:=zVv (TY J)
  let s :aZ →+* D[X] :=zOD
    (Polynomial.C.comp ((zVv J).comp znf))
    ![z7y,z1z (zVv J (z9v 2))]
  let subst:z3y (Fin 3) aZ →+* D[X] :=zOD s
    (fun i=>z1z (zVv J (z9v i)))
  let ev :D[X] →+* Q:=zqf d
    (z12 aQ Q (z9Y 0))
  have hs :ev.comp s=(z12 aQ Q).comp (z12 aZ aQ) := by
    apply zXT
    · intro a
      simp only [s,zQb,zTv,ev,z4Q,
        zJU]
      calc
        _=aL8 J (znf a) :=zmU hd (znf a)
        _ = _:= by
          change mkQ (baseChange (znf a)) =
            mkQ (znf (z12 FX aQ a))
          rw [zpw]
    · intro i
      simp only [s,zQb,zrD]
      fin_cases i
      · change ev z7y=z12 aQ Q (z9Y 0)
        simp [ev]
      · change ev (z1z (zVv J (z9v 2))) =
          z12 aQ Q (z9Y 1)
        simp only [ev,z4Q,zJU]
        exact (zmU hd _).trans (ds4 J)
  have hsubst:ev.comp subst=mkQ.comp (z12 (z3y (Fin 3) aZ) aRw) := by
    apply zXT
    · intro a
      change ev (zOD s _ (znf a)) =
        mkQ (zDK (z12 aZ aQ) (znf a))
      rw [zTv,zpw]
      exact zmU hs a
    · intro i
      change ev (zOD s _ (z9v i)) =
        mkQ (zDK (z12 aZ aQ) (z9v i))
      rw [zrD,z7N]
      change Polynomial.eval₂ d _ (z1z (zVv J (z9v i))) =
        mkQ (z9v i)
      rw [zJU]
      calc
        _=aL8 J (z9v i) :=zmU hd _
        _ = _:= by
          change mkQ (baseChange (z9v i))=mkQ (z9v i)
          rw [z7N]
  let M:Submonoid (z3y (Fin 3) aZ) :=(zgt aZ).map znf
  let:IsLocalization M aRw:=MvPolynomial.isLocalization (zgt aZ) aQ
  obtain ⟨a,rfl⟩:=zld (I:=TY J) q
  obtain ⟨⟨p,u⟩,hp⟩:=IsLocalization.surj M a
  refine ⟨mkQ (z12 (z3y (Fin 3) aZ) aRw u),
    (z0j aRw u).map mkQ,
    subst p,?_⟩
  change mkQ a*mkQ (z12 (z3y (Fin 3) aZ) aRw u)=ev (subst p)
  rw [← zok,hp]
  exact (zmU hsubst p).symm
private theorem bqo {A F G:Type} [za6 A] [zrb F] [zrb G]
  [zZE A F] [z0o A F] (S:Subfield G) (f :F →+* G)
  (h : ∀ a :A,f (z12 A F a)∈S) (z :F) :f z∈S:= by
 obtain ⟨a,b,_,rfl⟩:=IsFractionRing.div_surjective A z
 rw [map_div₀]
 exact S.div_mem (h a) (h b)
private theorem c4Q {A F:Type} [za6 A] [zrb F]
   (S:Subfield F) (f :A[X] →+* F)
   (hC : ∀ a,f (z1z a)∈S) (hX:f z7y∈S)
   (p:A[X]) :f p∈S:= by
 refine Polynomial.induction_on p hC (fun p q hp hq => ?_) (fun n a ha => ?_)
 · rw [zrl]
   exact S.add_mem hp hq
 · rw [pow_succ,← ztg,zok]
   exact S.mul_mem ha hX
variable {C₀:sQ} [Fact (z5o C₀)] {J:znc kM} {g:ℕ}
private abbrev a7W (R:wJ C₀ J g) :=UI.ek R
private theorem fXR (R:wJ C₀ J g) (a :FX) :
  a7W R (znf a)=amB R a := by
 simp only [UI.ek,zQb,LG,zTv]
 rfl
private theorem c8T (R:wJ C₀ J g) :
  a7W R (z9v 2)=aW2 R:= by
 simp only [UI.ek,zQb,LG,zrD]
 rfl
private theorem fXS (R:wJ C₀ J g) :
  zdq (a7W R)=J:= by
 ext p
 rw [zry]
 change zY7 (R:=y7 C₀) (K8 R) (LG C₀ p)=0↔p∈J
 have h:p∈J↔LG C₀ p∈zye {K8 R} :=
  Iff.of_eq (zPw (fun I:znc kM=>p∈I) R.contraction)
 exact (AdjoinRoot.mk_eq_zero.trans Ideal.mem_span_singleton.symm).trans h.symm
private theorem gtL (R:wJ C₀ J g)
   (S:Subfield (Jv (EC R)))
   (hroot : ∀ p:kM,IN (EC R) (a7W R p)∈S)
   (hspare :awC (EC R)∈S)
   (z :Jv (EC R)) :z∈S:= by
 let E :=EC R
 let F:=y7 C₀
 let:zrb E :=inferInstanceAs (zrb (EC R))
 let:zrb F:=inferInstanceAs (zrb (y7 C₀))
 let k :=IN E
 let kF:F →+* Jv E :=k.comp (AdjoinRoot.of (R:=y7 C₀) (K8 R))
 have hC:=bRL.proof C₀
 let:zZE (aZ ⧸ BI C₀) F:=(bv8 C₀ hC.kernel).toAlgebra
 let:z0o (aZ ⧸ BI C₀) F:=hC.localized
 have hseed (a :F) :kF a∈S:= by
   refine bqo (A:=aZ ⧸ BI C₀) S kF ?_ a
   intro q
   obtain ⟨p,rfl⟩:=zld q
   have heq :LG C₀ (pZ p)=z1z (O4 C₀ p) := by
     have h:=zmU cfB p
     change apf (pZ p)=z1z p at h
     rw [bqA,zQb]
     change (apf (pZ p)).map (O4 C₀)= _
     rw [h,zrL]
   change IN (EC R)
     ((zY7 (R:=y7 C₀) (K8 R)) (z1z (O4 C₀ p)))∈S
   have hp:=hroot (pZ p)
   simpa only [UI.ek,zQb,heq] using hp
 have hconstants (a :E) :k a∈S:= by
   obtain ⟨p,rfl⟩:=AdjoinRoot.mk_surjective (R:=y7 C₀) (g:=K8 R) a
   change (k.comp (zY7 (R:=y7 C₀) (K8 R))) p∈S
   apply c4Q S
   · exact hseed
   · change k (aW2 R)∈S
     simpa only [c8T] using hroot (z9v 2)
 change (zz5 (Jv E)) z∈S
 refine bqo (A:=E[X]) S (zz5 _) ?_ z
 intro p
 exact c4Q S (z12 E[X] (Jv E)) hconstants hspare p
private theorem eae {E :Type} [zrb E] (J:znc kM)
    (ρ:kM →+* E) (hker :zdq ρ=J)
    (b:aQ →+* Jv E)
    (hb:aYW (ρ.comp znf) (ρ (z9v 2)) b) :
    ∃ f :SI J →+* Jv E,zq4 f ∧
      f.comp (z12 aQ (SI J))=b ∧
      f.comp (aL8 J)=(IN E).comp ρ:= by
  let Q:=SI J
  let k :=IN E
  let ev :aRw →+* Jv E :=
    zOD b (fun i=>k (ρ (z9v i)))
  have hev :ev.comp baseChange=k.comp ρ:= by
    apply zXT
    · intro a
      simpa only [zQb,zpw,ev,zTv,
        k] using hb.1 a
    · intro i
      change zOD b (fun i=>k (ρ (z9v i)))
        (baseChange (z9v i))=k (ρ (z9v i))
      rw [z7N,zrD]
  have hkill:TY J≤zdq ev := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap,zEW,hev,
        zGm _ k.injective,hker]
    · apply Ideal.span_le.mpr
      rintro p ⟨rfl⟩
      change ev (Pp 2)=0
      simp only [Pp,zpO,ev,zrD,zTv]
      exact sub_eq_zero.mpr hb.2.1.symm
  let f :Q →+* Jv E :=zP2 (TY J) ev
    (fun _ h=>RingHom.mem_ker.mp (hkill h))
  have hfBase :f.comp (z12 aQ Q)=b:= by
    apply zz4
    intro a
    change ev (znf a)=b a
    exact zTv _ _ _
  have hfAmbient:f.comp (aL8 J)=k.comp ρ:=hev
  let D:=kM ⧸ J
  let:za6 D:=z0w J
  let:za6 D[X] :=zqU
  let j:D →+* E :=zP2 J ρ (fun p hp =>
    RingHom.mem_ker.mp (hker.symm ▸ hp))
  have hj:zq4 j :=
    RingHom.lift_injective_of_ker_le_ideal J _ hker.le
  let d:D →+* Q:=zP2 J (aL8 J) (fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((zPQ:J.map baseChange≤TY J) (z7X baseChange hp)))
  have hd:d.comp (zVv J)=aL8 J:=rfl
  let t:D[X] →+* Q:=zqf d
    (z12 aQ Q (z9Y 0))
  have hft:f.comp t=(z12 E[X] (Jv E)).comp (zhd j) := by
    apply z3l
    · apply Ideal.Quotient.ringHom_ext
      apply zz4
      intro p
      simp only [zQb,t,z4Q,zKC]
      rw [zJU,zrL]
      change f (d (zVv J p))=k (ρ p)
      exact zmU hfAmbient p
    · change f (zqf d
        (z12 aQ Q (z9Y 0)) z7y)= _
      rw [z4Q,Polynomial.eval₂_X]
      rw [zQb,zKC,zSo]
      exact (zmU hfBase _).trans hb.2.2
  have htinj:zq4 (f.comp t) := by
    rw [hft]
    exact (zxb E[X] (Jv E)).comp (zTo j hj)
  have hfinj:zq4 f := by
    apply (zLn f).mpr
    intro q hq
    obtain ⟨u,hu,p,hp⟩:=dLu J d hd q
    have hpzero : (f.comp t) p=0:= by
      change f (t p)=0
      rw [← show q*u=t p from hp,zok,hq,zero_mul]
    have hp0:p=0:=(zLn (f.comp t)).mp htinj p hpzero
    have hp' : q*u=t p:=hp
    rw [hp0,zhc] at hp'
    exact (hu.mul_left_eq_zero).mp hp'
  exact ⟨f,hfinj,hfBase,hfAmbient⟩
theorem proof :aiN.c2 := by
  intro C₀ hC J g R hfinite b hb
  let Q:=SI J
  have hb' : aYW ((a7W R).comp znf) (a7W R (z9v 2)) b:= by
    refine ⟨fun a => ?_,?_,hb.2.2⟩
    · simpa only [zQb,fXR] using hb.1 a
    · simpa only [c8T] using hb.2.1
  obtain ⟨f,hfinj,hfBase,hfAmbient⟩:=eae J (a7W R) (fXS R) b hb'
  let:IsDomain Q:=hfinj.isDomain f
  let:zAa aQ Q:=hfinite
  let:zrb Q:=(IsField.of_isDomain_of_finite aQ Q).toField
  have hsurj:zpX f := by
    intro z
    apply RingHom.mem_fieldRange.mp
    apply gtL R f.fieldRange _ _ z
    · intro p
      exact ⟨aL8 J p,zmU hfAmbient p⟩
    · exact ⟨z12 aQ Q (z9Y 0),
        (zmU hfBase _).trans hb.2.2⟩
  exact ⟨RingEquiv.ofBijective f ⟨hfinj,hsurj⟩,hfBase⟩
end
end czv
end
section
namespace bz2
noncomputable section
open cu Cu akS NS MvPolynomial
def bwA {n:ℕ} (i:Fin n) :e7 n :=
 z12 (N4 n) (e7 n) (z9v i)
def bhp (n:ℕ) :z3y (Fin n) (e7 n) :=
 ∑ i,znf (bwA i)*z9v i
private theorem arj {k E σ:Type*} [zrb k] [zrb E] [Fintype σ]
   (f :k →+* E) (x :σ→E) (t:E) {p:z3y σ k} {d:ℕ}
   (hp:p.IsHomogeneous d) :
   zSZ f (fun i=>t*x i) p=t^d*zSZ f x p:= by
 classical
 rw [eval₂_eq',eval₂_eq',zxw]
 refine zUo rfl fun e he => ?_
 have hd:e.degree=d:= by
   by_contra h
   exact (mem_support_iff.mp he) (hp.coeff_eq_zero h)
 rw [show (∏ i:σ,(t*x i)^e i)=t^d * ∏ i:σ,x i^e i by
   simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
     ← Finsupp.degree_eq_sum,hd]]
 ring
private theorem eyV {k E σ:Type*} [zrb k] [zrb E]
  (f :k →+* E) (I:znc (z3y σ k)) {p:z3y σ k} {d:ℕ}
  (hp:p∈I) (hd:p.totalDegree≤d) :
  zDK f (zyc d p)∈lW (I.map (zDK f)) := by
 have he :zDK f (zyc d p) =
    zyc d (zDK f p) := by
  ext e
  by_cases h:e.degree=d <;>
    simp only [coeff_homogeneousComponent,coeff_map,h,ite_true,ite_false,zhc]
 refine zCn ⟨zDK f p,d,z7X _ hp,?_,he⟩
 exact (zRS (z88 f p)).trans hd
private theorem dzM {k σ:Type*} [zrb k] [Finite σ]
   [LinearOrder σ] [WellFoundedGT σ] (I:znc (z3y σ k))
   (hI: (zIU I).natDegree≤1) (i:σ) :
   (zIU (KL I i)).natDegree=0:= by
 rcases eq_or_lt_of_le hI with h | h
 · exact YT.bmo I h i
 · apply za7
   have hcut:lW I≤KL I i:=zPQ
   refine (natDegree_affineHilbertPolynomial_le_of_le hcut).trans ?_
   rw [YT.bqR]
   omega
private abbrev aSI (n:ℕ) :=AlgebraicClosure (e7 n)
private theorem aOX {n:ℕ} (I:znc (N4 n))
   {x :Fin n→aSI n}
   (hx :x∈zSD (aSI n)
     (lW (I.map (zDK (z12 FX (e7 n))))))
   {i:Fin n} (hi:x i≠0) :
   (fun j=>(x i)⁻¹*x j)∈zSD (aSI n) (KL I i) := by
 change KL I i≤zdq (zOD (z12 FX (aSI n))
   (fun j=>(x i)⁻¹*x j))
 apply sup_le
 · apply Ideal.span_le.mpr
   rintro _ ⟨p,d,hp,hd,rfl⟩
   have he :=hx _ (eyV (z12 FX (e7 n)) I hp hd)
   rw [aeval_def,eval₂_map,← zYY] at he
   change zSZ (z12 FX (aSI n)) (fun j=>(x i)⁻¹*x j)
     (zyc d p)=0
   rw [arj _ x ((x i)⁻¹) (homogeneousComponent_isHomogeneous _ _),he,mul_zero]
 · apply Ideal.span_le.mpr
   rintro _ (rfl :_=z9v i - 1)
   change zSZ (z12 FX (aSI n)) (fun j=>(x i)⁻¹*x j)
     (z9v i - 1)=0
   rw [eval₂_sub,eval₂_X,eval₂_one,inv_mul_cancel₀ hi,sub_self]
private theorem dIq {k E σ:Type*} [zrb k] [zrb E] [zZE k E]
  [Finite σ] (J:znc (z3y σ k)) (hJ: (zIU J).natDegree=0)
  {x :σ→E} (hx :x∈zSD E J) (j:σ) :IsAlgebraic k (x j) := by
 let:zAa k (z3y σ k ⧸ J) :=
  moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
 let e : (z3y σ k ⧸ J) →ₐ[k] E :=zTA J (zIe x) hx
 have h:=(zmn (R:=k) (zVv J (z9v j))).map e
 change IsIntegral k (zIe x (z9v j)) at h
 rw [aeval_X] at h
 exact h.isAlgebraic
theorem gsE {n:ℕ} (I:znc (N4 n))
   (hI: (zIU I).natDegree≤1) :
   ahc (I.map (zDK (z12 FX (e7 n)))) (bhp n) := by
 classical
 have hl: (bhp n).IsHomogeneous 1 :=
   (homogeneousSubmodule (Fin n) (e7 n) 1).sum_mem
     fun j _=>isHomogeneous_C_mul_X (bwA j) j
 apply YT.bPG (K:=aSI n) _ hl
 intro x hx hz
 funext i
 change x i=0
 by_contra hi
 let E :=aSI n
 let u (j:Fin n) :E :=z12 (e7 n) E (bwA j)
 have hu₀:zlL FX (@bwA n) :=
   (algebraicIndependent_X (Fin n) FX).map'
     (f :=zE2 FX (N4 n) (e7 n))
     (zxb _ _)
 have hu:zlL FX u :=
   hu₀.map' (f :=zE2 FX (e7 n) E) (z12 (e7 n) E).injective
 let A:=algebraicClosure FX E
 have hlin:z14 A u:=hu.algebraicClosure.linearIndependent
 have hb:=aOX I hx hi
 let b (j:Fin n) :A:=⟨(x i)⁻¹*x j,mem_algebraicClosure_iff.mpr
   (dIq _ (dzM I hI i) hb j)⟩
 have hsum : ∑ j,u j*x j=0:= by
   simpa only [bhp,zdo,zok,aeval_C,aeval_X,u] using hz
 have hs : ∑ j,b j•u j=0:= by
   change ∑ j,((x i)⁻¹*x j)*u j=0
   simp_rw [ztg,zDE (x _) (u _)]
   rw [← zxw,hsum,mul_zero]
 have hzero :=(Fintype.linearIndependent_iff.mp hlin b hs) i
 have hbi: (x i)⁻¹*x i=(0:E) :=zPw Subtype.val hzero
 rw [inv_mul_cancel₀ hi] at hbi
 exact one_ne_zero hbi
end
end bz2
end
section
namespace bz2
noncomputable section
open cu Cu akS NS MvPolynomial
open scoped akS
private def bKg {n:ℕ} (B:znc (Gc n)) :znc (N4 n) :=
 B.comap (aa4 n)
private theorem eJT {n:ℕ} (B:znc (Gc n)) :
   (zIU (bKg B)).natDegree ≤
     (zIU B).natDegree := by
 let f :N4 n →ₐ[FX] Gc n:=zHw Sum.inr
 let g: (N4 n ⧸ bKg B) →ₐ[FX] tu B :=
   Ideal.quotientMapₐ B f le_rfl
 exact natDegree_affineHilbertPolynomial_le_of_injective g
   (Ideal.quotientMap_injective (I:=B) (f :=f.toRingHom))
private abbrev bFM {n:ℕ} (B:znc (Gc n)) :
   znc (z3y (Fin n) (e7 n)) :=
 (bKg B).map (zDK (z12 FX (e7 n)))
private def b1P {n:ℕ} (B:znc (Gc n)) :
   (z3y (Fin n) (e7 n) ⧸ bFM B) →ₐ[e7 n]
     Mb B:= by
 apply zTA _ (pD B)
 change bFM B≤zdq (pD B).toRingHom
 apply Ideal.map_le_iff_le_comap.mpr
 intro q hq
 have hq' : aa4 n q∈B:=hq
 change pD B (zDK (z12 FX (e7 n)) q)=0
 rw [c3x B,Ideal.Quotient.eq_zero_iff_mem.mpr hq',zhc]
private theorem d2U {n:ℕ} (B:znc (Gc n)) :
   b1P B (zVv (bFM B) (bhp n)) =
     aoe B:= by
 change pD B (bhp n)=aoe B
 unfold bhp aoe
 rw [zdo]
 apply zUo rfl
 intro i _
 simp only [zok,pD,aeval_C,aeval_X,bwA]
 exact (zd5 (A:=Mb B) _ _).symm
private theorem eyZ {n:ℕ} (B:znc (Gc n)) (d:ℕ) :
   (z9e (bFM B) d).map (b1P B).toLinearMap =
     aIU B d:= by
 rw [z9e,← Submodule.map_comp,aIU]
 congr 1
private theorem eNs {F A:Type} [zrb F] [za6 A] [zZE F A]
   (a :A) (W:zpI F A) (k :ℕ) :abb a W k≤abb a W (k+1) := by
 induction k with
 | zero=>exact le_sup_left
 | succ k ih =>
   exact sup_le_sup le_rfl (Submodule.map_mono ih)
private theorem dr0 {F A:Type} [zrb F] [za6 A] [zZE F A]
  (a :A) (W:zpI F A) (k :ℕ) {x y :A}
  (hx :x∈abb a W k) (hy :y∈abb a W k) :
  x+a*y∈abb a W (k+1) := by
 refine Submodule.add_mem _ (eNs a W k hx) ?_
 change a*y∈W ⊔ (abb a W k).map (LinearMap.mulLeft F a)
 exact Submodule.mem_sup.mpr ⟨0,W.zero_mem,a*y,⟨y,hy,rfl⟩,zero_add _⟩
private theorem ezk {F A σ:Type} [zrb F] [za6 A] [zZE F A]
   {I:znc (z3y σ F)} {ℓ:z3y σ F}
   (φ: (z3y σ F ⧸ I) →ₐ[F] A) (h:ahc I ℓ) :
   ∃ D:ℕ,∀ k :ℕ,(z9e I (D + k)).map φ.toLinearMap ≤
     abb (φ (zVv I ℓ)) ((z9e I D).map φ.toLinearMap) k := by
 obtain ⟨D,hD⟩:=h
 refine ⟨D,?_⟩
 intro k
 induction k with
 | zero=>exact le_rfl
 | succ k ih =>
   intro z hz
   obtain ⟨w,hw,rfl⟩:=Submodule.mem_map.mp hz
   obtain ⟨x,hx,y,hy,hxy⟩:=hD (D + k) (z8K D k) w hw
   change φ w∈_
   rw [hxy,zrl,zok]
   exact dr0 _ _ _
     (ih (zip hx)) (ih (zip hy))
theorem proof :akS.c1 := by
 intro n B _ hdim
 have h:=gsE (bKg B) ((eJT B).trans hdim)
 obtain ⟨D,hD⟩:=ezk (b1P B) h
 refine ⟨D,fun k => ?_⟩
 simpa only [eyZ,d2U] using hD k
end
end bz2
end
section
namespace aZa
noncomputable section
open K1 cu DQ MvPolynomial

open scoped Polynomial BigOperators
variable {n:ℕ}
private abbrev incl:=z12 L[X] FX
private theorem ayL (S:K[X]) : (S.map jz).eval center=kr S:= by
 rw [zhI]
 change S.eval₂ (incl.comp (Polynomial.C.comp (z12 K L))) (incl z7y) =
  incl (S.map (z12 K L))
 rw [← zly,← zem,z8i]
private theorem factorial_ne_zero {i:ℕ} (hi:i<p) : (i.factorial:FX)≠0:= by
 let:CharP FX p:=zgG jz.injective p
 induction i with
 | zero=>simp
 | succ i ih =>
   have hc: ((i+1 :ℕ) :FX)≠0:= by
     intro h
     exact (ziF hi) (zTm (ztH i) ((zX2 FX p _).mp h))
   simpa only [zwO,z2R] using mul_ne_zero hc (ih (zws hi))
end
end aZa
end
section
set_option maxHeartbeats 800000
namespace bao
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
section Family
variable {k σ τ:Type} [zrb k]
local notation "P" => MvPolynomial τ k
local notation "F" => FractionRing (MvPolynomial τ k)
local notation "A" => MvPolynomial σ k
local notation "T" => MvPolynomial σ (MvPolynomial τ k)
local notation "U" => MvPolynomial σ (FractionRing (MvPolynomial τ k))
private def Xm:A →+* T:=zDK znf
private def azT (s :zJe τ) (p:τ→A) :T :=
 ∑ j∈s,C (z9v j)*Xm (p j)
def aNT (s :zJe τ) (p:τ→A) (c:τ→k) :A :=
 ∑ j∈s,C (c j)*p j
def aUA (s :zJe τ) (p:τ→A) :U :=
 z12 T U (azT s p)
private def reduce (I:znc A) :T →+* z3y τ (A ⧸ I) :=
 (zDK (zVv I)).comp (commAlgEquiv k σ τ).toRingHom
@[simp] private theorem bLc (I:znc A) (r :P) :
   reduce I (C r)=zDK (z12 k (A ⧸ I)) r := by
  change zDK (zVv I) (commAlgEquiv k σ τ (C r))= _
  rw [commAlgEquiv_C,MvPolynomial.map_map]
  rfl
@[simp] private theorem ceS (I:znc A) (v :A) :
    reduce I (Xm (τ:=τ) v)=(C (zVv I v) :z3y τ (A ⧸ I)) := by
  change (reduce I).comp Xm v=(C.comp (zVv I)) v
  congr 1
  apply zXT
  · intro r
    simp [ Xm]
    rfl
  · intro i
    simp [reduce,Xm]
private theorem a4S (I:znc A) :zdq (reduce (τ:=τ) I)=I.map Xm:= by
 let e :=commAlgEquiv k σ τ
 have hcomp:e.toRingHom.comp Xm=(C:A →+* z3y τ A) := by
   apply zXT
   · intro r
     simp [e,Xm]
   · intro i
     simp [e,Xm]
 change zdq ((zDK (zVv I)).comp e.toRingHom)= _
 rw [← zEW,MvPolynomial.ker_map,Ideal.mk_ker,
   ← hcomp,← z0L]
 exact zFA (I:=I.map Xm) e.toRingHom e.bijective
private theorem b2E : (z12 T U).comp Xm=zDK (z12 k F) := by
 change (zDK (z12 P F)).comp Xm= _
 apply zXT
 · intro r
   simp [ Xm]
   rfl
 · intro i
   simp [ Xm]
private theorem cNV (v :A) :
  z12 T U (Xm v)=zDK (z12 k F) v :=
 zmU b2E v
private theorem d5z (I:znc A) (s :zJe τ) (p:τ→A) :
   (I.map Xm ⊔ zye {azT s p}).map (z12 T U) =
     I.map (zDK (z12 k F)) ⊔ zye {aUA s p} := by
 rw [Ideal.map_sup,z0L,b2E,Ideal.map_span,zyk]
 rfl
theorem d6e (s :zJe τ) (p:τ→A) :
   aUA s p = ∑ j∈s,C (z12 P F (z9v j)) *
     zDK (z12 k F) (p j) := by
 unfold aUA azT
 rw [zdo]
 apply zUo rfl
 intro j _
 rw [zok,cNV,zu8,zpw]
theorem d6f [Finite σ] (I:znc A) [I.IsPrime]
   (hdim: (zIU I).natDegree≤1)
   (s :zJe τ) (p:τ→A) {j:τ} (hj:j∈s) (hone :p j=1) :
   zAa F (U ⧸
     (I.map (zDK (z12 k F)) ⊔ zye {aUA s p})) := by
 classical
 let M:=(zgt P).map (C (σ:=σ))
 let I' : znc T:=I.map Xm
 have hprime :I'.IsPrime := by
   rw [show I' = I.map Xm from rfl,← a4S]
   exact (RingHom.ker_isPrime (reduce I))
 have hdisj:Disjoint (M:Set T) (I' : Set T) := by
   refine Set.disjoint_left.mpr ?_
   intro x hx hi
   change x∈(zgt P).map (C (σ:=σ)) at hx
   obtain ⟨r,hr,rfl⟩:=hx
   change C r∈I.map Xm at hi
   rw [← a4S,zry,bLc] at hi
   exact zyw hr
     ((MvPolynomial.map_injective _ (z12 k (A ⧸ I)).injective) (hi.trans (zhc _).symm))
 have hpre :azT s p∉I' := by
   change azT s p∉I.map Xm
   rw [← a4S,zry]
   intro hh
   have h:=zPw (fun p:z3y τ (A ⧸ I)=>p.coeff (zhf j 1)) hh
   simp only [azT,zdo,zok,bLc,ceS,z7N,coeff_sum,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at h
   rw [zpa j hj] at h
   · simp [hone] at h
   · intro i _ hi
     rw [zDE (z9v i),coeff_C_mul,MvPolynomial.coeff_single_X]
     simp [hi]
 have hext:I'.map (z12 T U)=I.map (zDK (z12 k F)) := by
   rw [show I' = I.map Xm from rfl,z0L,b2E]
 have hprime' := znL M U I' hprime hdisj
 have hproper :aUA s p∉I'.map (z12 T U) := by
   change azT s p∉(I'.map (z12 T U)).under T
   rwa [ztT M U hprime hdisj]
 rw [hext] at hprime' hproper
 apply natDegree_affineHilbertPolynomial_eq_zero_iff.mp
 apply za7
 have h:=(zAy
   hprime' hproper (le_refl (aUA s p).totalDegree)).1
 rw [Ey.ZI] at h
 exact h.trans (by omega)
private theorem gqn (I:znc A) (s :zJe τ) (p:τ→A) (c:τ→k) :
    shift (fun j=>z12 k (A ⧸ I) (c j)) (reduce I (azT s p)) =
      C (zVv I (aNT s p c)) +
        ∑ j∈s,C (zVv I (p j))*z9v j:= by
  let q:=zVv I
  calc
    _ = ∑ j∈s,(C (q (C (c j)*p j))+C (q (p j))*z9v j) := by
      simp only [azT,zdo,zok,bLc,ceS,z7N,gqb,ddR]
      refine zUo rfl fun j _ => ?_
      rw [add_mul]
      change z9v j*C (q (p j))+C (q (C (c j)))*C (q (p j))= _
      rw [zDE (z9v j),zV7]
    _ = _:= by
      rw [zfW,← zdo,← zdo]
      rfl
theorem d6g (I:znc A) [I.IsPrime]
    (s :zJe τ) (p:τ→A) (c:τ→k) (hproper :aNT s p c∉I)
    {ι:Type} [Fintype ι] (v :ι→A)
    (hv :z14 k (fun i =>
      zVv (I ⊔ zye {aNT s p c}) (v i))) :
    z14 F fun i =>
      zVv
        (I.map (zDK (z12 k F)) ⊔ zye {aUA s p})
        (zDK (z12 k F) (v i)) := by
  classical
  let M:=(zgt P).map (C (σ:=σ))
  let J:znc T:=I.map Xm ⊔ zye {azT s p}
  let JF:=J.map (z12 T U)
  let qF:=zVv JF
  rw [← d5z]
  apply Fintype.linearIndependent_iff.mpr
  intro b hb
  change ∑ i,b i•qF (zDK (z12 k F) (v i))=0 at hb
  obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite (zgt P) b
  choose a ha using hd
  let S:T := ∑ i,C (a i)*Xm (v i)
  have hS:z12 T U S∈JF:= by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qF (z12 T U S)=0
    have hterm : ∀ i,qF (z12 T U (C (a i)*Xm (v i))) =
        (d.val•b i)•qF (zDK (z12 k F) (v i)) := by
      intro i
      rw [zok,zok,cNV,zu8,
        zpw,ha i,← qF.map_mul,← MvPolynomial.smul_eq_C_mul]
      exact map_smul (zvR F JF) _ _
    have hs (i:ι) :d.val•b i=z12 P F d.val*b i :=
      zd5 d.val (b i)
    simp only [S,zdo,hterm,hs,mul_smul,← Finset.smul_sum,hb,smul_zero]
  obtain ⟨m,hm,hmul⟩:=(IsLocalization.algebraMap_mem_map_algebraMap_iff M U J S).mp hS
  change m∈(zgt P).map (C (σ:=σ)) at hm
  obtain ⟨r,hr,rfl⟩:=hm
  obtain ⟨x,hx,y,hy,hxy⟩:=Submodule.mem_sup.mp hmul
  obtain ⟨H,hH⟩:=Ideal.mem_span_singleton.mp hy
  have hx0:reduce (τ:=τ) I x=0:= by
    change x∈I.map Xm at hx
    rwa [← a4S,zry] at hx
  let translate :=shift (fun j:τ=>z12 k (A ⧸ I) (c j))
  have he :translate (reduce I (C r*S)) =
      translate (reduce I (azT s p))*translate (reduce I H) := by
    rw [← hxy,zrl,hx0,zero_add,hH,zok,zok,zDE]
  have he' : ∑ i,zDK (z12 k (A ⧸ I)) (shift c (r*a i)) *
        C (zVv I (v i)) =
      (C (zVv I (aNT s p c)) +
        ∑ j∈s,C (zVv I (p j))*z9v j) *
        translate (reduce I H) := by
    rw [show translate (reduce I (azT s p))= _ from gqn I s p c] at he
    refine Eq.trans ?_ he
    dsimp only [S]
    rw [zxw,zdo,zdo]
    apply zUo rfl
    intro i _
    rw [← ztg,← C.map_mul]
    simp only [translate,zok,bLc,ceS,gqh,ddR]
  let q:=Ideal.Quotient.factorₐ k (zPQ:I≤I ⊔ zye {aNT s p c})
  have hq:q (zVv I (aNT s p c))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (zs0 (z5J _))
  have hzero :=bX4 q (mt Ideal.Quotient.eq_zero_iff_mem.mp hproper)
    hq (by exact hv) s (fun j=>zVv I (p j)) _ _ he'
  intro i
  have hai:a i=0:= by
    have hh:r*a i=0:=gqg c (by simpa using hzero i)
    exact (mul_eq_zero.mp hh).resolve_left (zyw hr)
  have hh:=ha i
  rw [hai,zhc,zd5] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left
    ((zw1 _ (zxb P F)).mpr (zyw d.property))
end Family
end
end bao
end
section
namespace bao
noncomputable section
open MvPolynomial aR dN BO GJ axe
private def exponent (a :Shape) :uL a ↪ (Fin 4 →₀ ℕ) where
 toFun m:=Finsupp.equivFunOnFinite.symm fun i=>(m i).val
 inj' := by
  intro x y h
  funext i
  apply Fin.ext
  exact zmU h i
private def aMv (k :Type) [zrb k] {a :Shape} (m:uL a) :
   z3y (Fin 4) k :=
 ∏ i:Fin 4,z9v i^(m i).val
private theorem d4d {k :Type} [zrb k]
    {Q:z3y (Fin 4) k} {a :Shape} (hQ:bQW Q a) :
    ∃ c:uL a→k,aNT (Bz a) (aMv k) c= Q:= by
  classical
  refine ⟨fun m=>Q.coeff (exponent a m),?_⟩
  have hexp (m:uL a) (i:Fin 4) :exponent a m i=(m i).val :=rfl
  have hsupport :Q.support⊆(Bz a).map (exponent a) := by
    intro s hs
    have hb: (∑ i:Fin 4,s i)≤a.b:= by
      simpa [z9d] using (le_totalDegree hs).trans hQ.1
    have hj: (∑ i:Fin 4,i.val*s i)≤a.j:= by
      simpa [Finsupp.weight_apply,z9d,zVT,Nat.mul_comm] using
        (le_weightedTotalDegree Fin.val hs).trans hQ.2.1
    have ht:s 3≤a.t:=(monomial_le_degreeOf 3 hs).trans hQ.2.2
    let m:uL a := fun i =>
      ⟨s i,Nat.lt_succ_of_le ((zfK
        (f := fun j:Fin 4=>s j) (fun j _=>zD0 (s j)) (Finset.mem_univ i)).trans hb)⟩
    refine Finset.mem_map.mpr ⟨m,?_,Finsupp.ext fun _=>rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ m,hb,hj,ht⟩
  have hsum:=Finset.sum_subset (f := fun s=>monomial s (Q.coeff s)) hsupport (by
    intro s _ hs
    rw [notMem_support_iff.mp hs,zhc])
  rw [Finset.sum_map] at hsum
  calc
    aNT (Bz a) (aMv k) (fun m=>Q.coeff (exponent a m)) =
        ∑ m∈Bz a,monomial (exponent a m) (Q.coeff (exponent a m)) := by
      unfold aNT aMv
      apply zUo rfl
      intro m _
      rw [monomial_eq,z6B _ _ (fun _=>zJx _)]
      simp only [hexp]
    _= Q:=hsum.symm.trans Q.as_sum.symm
theorem proof :axe.c2 := by
 classical
 intro k _ I Q a hI hdim _ hproper hfit
 let:I.IsPrime :=hI
 obtain ⟨c,hc⟩:=d4d hfit
 let z :uL a := fun _=>0
 have hz :z∈Bz a := by simp [z,Bz]
 have hone :aMv k z=1 := by simp [aMv,z]
 have hgen:aUA (Bz a) (aMv k)=a3g k a := by
   rw [d6e,a3g]
   simp [aMv]
 let J:=I ⊔ zye {Q}
 have hdimJ: (zIU J).natDegree=0:= by
   have h:=(zAy
     hI hproper (le_refl Q.totalDegree)).1
   exact za7 (h.trans (by omega))
 let:zAa k (z3y (Fin 4) k ⧸ J) :=
   natDegree_affineHilbertPolynomial_eq_zero_iff.mp hdimJ
 let:=d6f I hdim (Bz a) (aMv k) hz hone
 let b:=Module.finBasis k (z3y (Fin 4) k ⧸ J)
 choose v hv using fun i=>zld (b i)
 have hlin:z14 k (fun i=>zVv J (v i)) := by
   simpa only [hv] using b.linearIndependent
 have hlin' := d6g I (Bz a) (aMv k) c
   (hc.symm ▸ hproper) v (hc.symm ▸ hlin)
 unfold bHl
 rw [← hgen]
 simpa only [Fintype.card_fin] using hlin'.fintype_card_le_finrank
end
end bao
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace as6
noncomputable section
open aR dN rW Polynomial
@[simp] theorem bxK (P:n8) [P.IsPrime] (H :af 4) :
   aQP P (ee P H)=Zx P H := by
  unfold aQP ee
  rw [zQb,IsFractionRing.lift_algebraMap]
  rfl
theorem bYq (P:n8) [P.IsPrime] (H :af 4) :
  Zx P H=0↔bC H∈P:= by
 change z12 (GeoJets ⧸ P) (tJ P) (zVv P (bC H))=0↔_
 rw [zVB _ (zxb (GeoJets ⧸ P) (tJ P)),
  Ideal.Quotient.eq_zero_iff_mem]
theorem bgQ (P:n8) [P.IsPrime] (H :af 4) :
  ee P H=0↔bC H∈P:= by
 rw [← zVB _ (aQP P).injective,bxK,bYq]
@[simp] theorem gBL (P:n8) [P.IsPrime] (a :ao) :
   aQP P (z12 ao (am4 P) a)=CX P a := by
  change aQP P (ee P (znf (z1z a)))= _
  rw [bxK]
  simp [Zx,CX,ni]
@[simp] theorem gBK (P:n8) [P.IsPrime] :
   aQP P (KK (ee P))=K4 P (znf rI) := by
  rw [KK,bxK]
  simp [Zx,rI]
@[simp] theorem gBM (P:n8) [P.IsPrime] (i:Fin 4) :
   aQP P (ajH (ee P) i)=K4 P (z9v i) := by
  rw [ajH,bxK]
  simp [Zx]
theorem factorial_ne_zero {F:Type} [zrb F] (k :ao →+* F) {n:ℕ}
  (h:n<K1.p) : (n.factorial:F)≠0:= by
 rw [← zGu k]
 exact (zw1 k k.injective).mpr (lB.ahA h)
theorem bG3 {F:Type} [za6 F] {M:ℕ} (x :F) (a :Fin M→F)
  (hM:0<M) : (ahG x a).natDegree<M:= by
 unfold ahG
 refine lt_of_le_of_lt (zMZ _ (n:=M - 1) _ ?_) (by omega)
 intro i _
 have hterm : (C (a i)*(z7y (R:=F)-Polynomial.C x)^i.val).natDegree≤ i.val := by
  apply natDegree_mul_le.trans
  simp only [natDegree_C,zero_add]
  simpa only [Nat.mul_one] using zxc i.val (natDegree_X_sub_C_le x)
 exact hterm.trans (Nat.le_pred_of_lt i.isLt)
theorem bG4 {F:Type} [za6 F] {M:ℕ} (x :F) (a :Fin M→F)
   (i:Fin M) : (z75 i.val (ahG x a)).eval x=a i:= by
 classical
 have h:zcJ x (ahG x a) = ∑ j,monomial j.val (a j) := by
   simp only [ahG,zdo,taylor_mul,taylor_pow,taylor_C,zpO,
     taylor_X,add_sub_cancel_right,C_mul_X_pow_eq_monomial]
 rw [← zWQ,h,zaW,zi6 i]
 · simp
 · intro j _ hij
   simp [coeff_monomial,show j.val≠i.val from fun he=>hij (Fin.ext he)]
 · simp
theorem cZs {F E :Type} [za6 F] [za6 E] (k :F →+* E)
  {M:ℕ} (x :F) (a :Fin M→F) :
  (ahG x a).map k=ahG (k x) (fun i=>k (a i)) := by
 change zhd k (ahG x a)= _
 simp only [ahG,zdo,zok,zkq,zpO,zKC,zrL,zSo]
theorem aVM {F E :Type} [zrb F] [zrb E] (k :F →+* E) (a :ao →+* F)
   (H :af 4) (U:F[X]) :
   (jW a H U).map k=jW (k.comp a) H (U.map k) := by
 unfold jW
 change zhd k (zSZ _ _ H)= _
 rw [zUe]
 have hm: (zhd k).comp (zhd a) =
     zhd (k.comp a) := by
   apply zz4
   intro q
   exact Polynomial.map_map a k q
 simp only [hm,zKC,← zvb]
private theorem anS {F:Type} [zrb F] [zZE ao F]
   (D:zvY ao F F) (s v :F) (a :ℕ) :
   s*(s*D (s^a*v))-(a :F)*(s*D s)*(s^a*v) =
     s^(a+2)*D v := by
 cases a with
 | zero=>simp [pow_two,mul_assoc]
 | succ a =>
   rw [D.leibniz,D.leibniz_pow,Nat.succ_sub_one,pow_add s (a+1) 2,pow_succ' s a]
   simp only [zs5,zVT,zg0]
   ring
theorem cVU {F:Type} [zrb F] [zZE ao F]
   (e :af 4 →+* F) (g:af 4) (D:zvY ao F F)
   (action : ∀ H,e (zai g)*D (e H)=e (u6 g H)) (n:ℕ) :
   e (su g n) =
     e (zai g)^(2*n)*((D:F→F)^[n]) (ajH e 0) := by
 induction n with
 | zero=>simp [su,ajH]
 | succ n ih =>
   simp only [su,aqZ,zpO,zok,zGu,← action]
   rw [ih,anS,zLk,
     show 2*(n+1)=2*n+2 by omega]
theorem gpF {H :af 4} {B:ℕ} (h:tB H B) :
    tB (zai H) B:= by
  intro m hm
  rw [zuk,zai,zcl] at hm
  have hsrc :=h _ (MvPolynomial.mem_support_iff.mpr (z67 hm))
  have hweight (w:Fin 4→ℕ) :
      (m+Finsupp.single (3:Fin 4) 1).sum (fun i k=>w i*k) =
        m.sum (fun i k=>w i*k)+w 3:= by
    rw [Finsupp.sum_add_index' (fun i=>zvM (w i)) (fun i b c=>Nat.mul_add (w i) b c),
      Finsupp.sum_single_index (h:= fun i k=>w i*k) (zvM _),zqe]
  rw [hweight] at hsrc
  change ((zai H).coeff m).natDegree+_≤B
  rw [zai,zcl]
  have hd:=natDegree_mul_le (p:=H.coeff (m+Finsupp.single 3 1))
    (q:=(m 3:ao[X])+1)
  have hc: ((m 3:ao[X])+1).natDegree=0:= by
    rw [← zg0,natDegree_natCast]
  rw [hc,z0a] at hd
  omega
theorem epq {H :af 4} {B:ℕ} (h:tB H B) (r :ℕ) :
   tB ((zai^[r]) H) B:= by
 induction r with
 | zero=>exact h
 | succ r ih=>simpa only [Function.iterate_succ_apply'] using gpF ih
end
end as6
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace as6
noncomputable section
open aR dN rW Polynomial
def c1 :Prop :=
  ∀ (g:af 4) (P:n8) (_hp:P.IsPrime),
    bC g∈P→bC (zai g)∉P→ Invariant g P →
    ∃ D:zvY ao (am4 P) (am4 P),
      D (KK (ee P))=1 ∧
      (∀ i:Fin 3,D (ajH (ee P) i.castSucc) =
        ((i.val+1 :ℕ) :am4 P)*ajH (ee P) i.succ) ∧
      ∀ H :af 4,ee P (zai g)*D (ee P H)=ee P (u6 g H)
def c2 :Prop :=
  ∀ (F:Type) [zrb F] [zZE ao F] (D:zvY ao F F) (x y :F),
    D x=1→((D:F→F)^[bf]) y=0 →
    ∀ (H :af 4) (B:ℕ),tB H B→B+3<K1.p →
      zSZ (zEU x).toRingHom
        (fun i=>ZD D y i.val) H=0 →
      jW (z12 ao F) H (aHA D x y)=0
def c3:Prop :=
  ∀ (g:af 4) (P:n8) (_hp:P.IsPrime),
    bC g∈P→bC (zai g)∉P →
    ∀ S:ao[X],S.natDegree<bf→P≤Ch S →
      cK (zai g) S≠0 →
      Gp S∈zSD ao
        (Zv (CX P) (ab2 (Zx P) g))
private theorem c8X (P:n8) (H :af 4) :
   zSZ (zEU (KK (ee P))).toRingHom
     (ajH (ee P)) H=ee P H := by
 change zOD _ _ H=ee P H
 have hc: (zEU (KK (ee P))).toRingHom =
     (ee P).comp MvPolynomial.C:= by
   apply z86
   · intro a
     simp only [ziQ,zlv,aeval_C,zQb]
     rfl
   · simp [KK]
 rw [hc]
 have h:zOD ((ee P).comp znf)
     (ajH (ee P))=ee P:= by
   apply zXT <;> simp [ajH]
 rw [h]
private theorem cVf {F:Type} [zrb F] [zZE ao F]
    (e :af 4 →+* F) (D:zvY ao F F)
    (shift : ∀ i:Fin 3,D (ajH e i.castSucc) =
      ((i.val+1 :ℕ) :F)*ajH e i.succ) (i:Fin 4) :
    ZD D (ajH e 0) i.val=ajH e i:= by
  have raw (j:Fin 4) : ((D:F→F)^[j.val]) (ajH e 0) =
      (j.val.factorial:F)*ajH e j:= by
    induction j using Fin.induction with
    | zero=>simp
    | succ j ih =>
      rw [Fin.val_succ,zLk,← Fin.val_castSucc j,ih]
      simp only [D.leibniz,D.map_natCast,zs5,mul_zero,z0a,shift,
        Fin.val_castSucc,zwO,z2R]
      ring
  have hfact :=factorial_ne_zero (z12 ao F)
    (i.isLt.trans (by decide :4<K1.p))
  rw [ZD,raw i,zE5 _ hfact]
private theorem cFc (P:n8) [P.IsPrime] (g:af 4) :
  (ab2 (ee P) g).map (aQP P)=ab2 (Zx P) g:= by
 unfold ab2 KK
 rw [cZs]
 simp only [map_div₀,zkq,zGu,bxK]
end
end as6
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace cyv
noncomputable section
open aR dN rW as6 aKq
open nonZeroDivisors
private def rowJet {F:Type} [za6 F] (g:af 4) (e :Chart g →+* F) :
    af 4 →+* Dual F where
  toFun H :=(e (incl g H),e (D g (incl g H)))
  map_zero' := by
    apply zMz
    · change e (incl g 0)=0
      simp
    · change e (D g (incl g 0))=0
      simp
  map_one' := by
    apply zMz
    · change e (incl g 1)=1
      simp
    · change e (D g (incl g 1))=0
      rw [map_one,show D g 1=0 from by simpa only [Nat.cast_one] using cxr g 1,
        zhc]
  map_add' H J:= by
    apply zMz
    · change e (incl g (H+J))=e (incl g H)+e (incl g J)
      simp only [zrl]
    · change e (D g (incl g (H+J)))=e (D g (incl g H))+e (D g (incl g J))
      simp only [zrl]
  map_mul' H J:= by
    apply zMz
    · change e (incl g (H*J))=e (incl g H)*e (incl g J)
      simp only [zok]
    · change e (D g (incl g (H*J))) =
        e (incl g H)*e (D g (incl g J))+e (D g (incl g H))*e (incl g J)
      simp only [zok,bQM,zrl]
private theorem bFG {A F:Type} [za6 A] [zrb F] [zZE A F]
  [z0o A F] (j:A →+* Dual F)
  (hfst : ∀ a,(j a).fst=z12 A F a) :
  ∃ J:F →+* Dual F,(∀ a,J (z12 A F a)=j a) ∧ ∀ z,(J z).fst=z := by
 have hu (a :zgt A) :zWB (j a) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst,hfst]
  exact z0j F a
 let J:F →+* Dual F:=zvq hu
 have hJ (a :A) :J (z12 A F a)=j a :=zX4 hu a
 refine ⟨J,hJ,?_⟩
 have he : (zx5 F F F).toRingHom.comp J=zz5 F:= by
  apply zuW (zgt A)
  apply zz4
  intro a
  change (J (z12 A F a)).fst=z12 A F a
  rw [hJ,hfst]
 exact zmU he
private def dWq {k F:Type} [za6 k] [za6 F] [zZE k F]
    (J:F →+* Dual F) (hfst : ∀ z,(J z).fst=z)
    (hconst : ∀ a :k,(J (z12 k F a)).snd=0) :zvY k F F :=
  Derivation.mk'
    { toFun:= fun z=>(J z).snd
      map_add' := fun x y=> by rw [zrl,TrivSqZeroExt.snd_add]
      map_smul' := fun a x=> by
        change (J (a•x)).snd=a•(J x).snd
        rw [zd5,zok]
        change (J (z12 k F a)).fst*(J x).snd +
          (J (z12 k F a)).snd*(J x).fst=a•(J x).snd
        rw [hfst,hconst,zero_mul,z0a,zd5] }
    (fun x y=> by
      change (J (x*y)).snd=x*(J y).snd+y*(J x).snd
      rw [zok]
      change (J x).fst*(J y).snd+(J x).snd*(J y).fst= _
      rw [hfst,hfst,zDE (J x).snd y])
private theorem dHZ {A F:Type} [za6 A] [zrb F] [zZE A F]
   [z0o A F] [zZE ao F] (g:af 4)
   (f :af 4 →+* A) (hf :zpX f) (e :Chart g →+* F)
   (he : ∀ H,e (incl g H)=z12 A F (f H))
   (hstable : ∀ H,z12 A F (f H)=0→e (D g (incl g H))=0)
   (hconst : ∀ a :ao,z12 A F (f (znf (z1z a))) =
     z12 ao F a) :
   ∃ δ:zvY ao F F,∀ H,δ (z12 A F (f H))=e (D g (incl g H)) := by
 let j₀:=rowJet g e
 have hker :zdq f≤zdq j₀:= by
   intro H hH
   have hz :z12 A F (f H)=0:= by rw [RingHom.mem_ker.mp hH,zhc]
   apply RingHom.mem_ker.mpr
   apply zMz
   · exact (he H).trans hz
   · exact hstable H hz
 let j:A →+* Dual F:=f.liftOfSurjective hf ⟨j₀,hker⟩
 have hj (H :af 4) :j (f H)=j₀ H :=RingHom.liftOfSurjective_comp_apply f hf _ H
 have hjfst (a :A) : (j a).fst=z12 A F a := by
   obtain ⟨H,rfl⟩:=hf a
   rw [hj]
   exact he H
 obtain ⟨J,hJ,hJfst⟩:=bFG j hjfst
 have hrow (H :af 4) :J (z12 A F (f H))=j₀ H :=(hJ (f H)).trans (hj H)
 have hc (a :ao) : (J (z12 ao F a)).snd=0:= by
   rw [← hconst,hrow]
   change e (D g (constants g (z1z a)))=0
   rw [bQL,zJH]
   change e (incl g (znf 0))=0
   simp only [zhc]
 exact ⟨dWq J hJfst hc,fun H=>zPw TrivSqZeroExt.snd (hrow H)⟩
set_option maxHeartbeats 800000 in
theorem proof :as6.c1 := by
 intro g P hp _hg hs hi
 let _:P.IsPrime :=hp
 let F:=am4 P
 let f :af 4 →+* bQA P:=(Zx P).rangeRestrict
 have hf :zpX f :=(Zx P).rangeRestrict_surjective
 have hs' : ee P (zai g)≠0:= fun hz=>hs ((bgQ P _).mp hz)
 let e :Chart g →+* F:=ztx (zai g) (g:=ee P) hs'.isUnit
 have he (H :af 4) :e (incl g H)=ee P H :=zaz _ _ _
 have hflow (H :af 4) :ee P (zai g)*e (D g (incl g H)) =
     ee P (u6 g H) := by
   simpa only [zok,he] using DFunLike.congr_arg e (bQK g H)
 have hstable (H :af 4) (hz :ee P H=0) :e (D g (incl g H))=0:= by
   have ht:=(bgQ P (u6 g H)).mpr (hi H ((bgQ P H).mp hz))
   exact (mul_eq_zero.mp ((hflow H).trans ht)).resolve_left hs'
 obtain ⟨δ,hδ⟩:=dHZ g f hf e he hstable (fun _=>rfl)
 have hδrow (H :af 4) :δ (ee P H)=e (D g (incl g H)) :=hδ H
 refine ⟨δ,?_,?_,fun H=> by rw [hδrow,hflow]⟩
 · change δ (ee P (znf z7y))=1
   rw [hδrow]
   change e (D g (constants g z7y))=1
   rw [bQL,zBT]
   change e (incl g (znf 1))=1
   simp only [map_one]
 · intro i
   change δ (ee P (z9v i.castSucc)) =
     ((i.val+1 :ℕ) :F)*ee P (z9v i.succ)
   rw [hδrow,bja,zok,zGu,he]
end
end cyv
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace cyw
noncomputable section
open aR rW as6 Polynomial
variable {F:Type} [zrb F] [zZE ao F]
private theorem natCast_ne_zero {n:ℕ} (hn:0<n) (hp:n<K1.p) :
   (n:F)≠0:= by
 intro h
 have hf :=factorial_ne_zero (z12 ao F) hp
 cases n with
 | zero=>omega
 | succ n=>exact hf (by rw [Nat.factorial_succ,Nat.cast_mul,h,zero_mul])
variable (D:zvY ao F F)
private def Oj:Subsemiring F[X] where
 carrier := {P | ∀ n,D (P.coeff n)=P.derivative.coeff n}
 zero_mem' n:= by simp
 one_mem' n:= by
  rw [derivative_one,zO6,coeff_one]
  split_ifs <;> simp
 add_mem' {P Q} hP hQ n:= by
  simp only [coeff_add,zrl,hP n,hQ n]
 mul_mem' {P Q} hP hQ n:= by
  have hMul (a b:F) :D (a*b)=a*D b+D a*b:= by
   rw [D.leibniz,zs5,zs5,zDE b (D a)]
  change D ((P*Q).coeff n)=(P*Q).derivative.coeff n
  simp only [coeff_mul,zdo,hMul,hP _,hQ _,zAg,coeff_add,
   zfW]
  abel
omit [zZE ao F] in
private theorem b5P (i j:ℕ) (P:F[X]) :
  z75 i (z75 j P)=z75 j (z75 i P) := by
 have hi:=z5U (hasseDeriv_comp (R:=F) i j) P
 have hj:=z5U (hasseDeriv_comp (R:=F) j i) P
 simp only [LinearMap.comp_apply,zqa] at hi hj
 rw [hi,hj,Nat.add_comm j i,Nat.choose_symm_add (a :=i) (b:=j)]
private theorem b5Q {P:F[X]} (hP:P∈Oj D) (i:ℕ) :
  z75 i P∈Oj D:= by
 intro n
 rw [← hasseDeriv_one',b5P 1 i,hasseDeriv_one',hasseDeriv_coeff,
  hasseDeriv_coeff,D.leibniz,D.map_natCast,zs5,zs5,
  mul_zero,z0a,hP (n+i)]
private theorem gqv (x :F) (hx :D x=1) (b:ao[X]) :
   zcJ x (b.map (z12 ao F))∈Oj D:= by
 have hX: ((z7y:F[X])+C x)∈Oj D:= by
   intro n
   simp only [coeff_add,derivative_X_add_C,coeff_X,coeff_C,coeff_one]
   split_ifs <;> simp_all
 induction b using Polynomial.induction_on' with
 | add a b ha hb =>
   simpa only [Polynomial.map_add,zrl] using (Oj D).add_mem ha hb
 | monomial n a =>
   rw [Polynomial.map_monomial,taylor_monomial]
   refine (Oj D).mul_mem (fun j => ?_) ((Oj D).pow_mem hX n)
   simp only [coeff_C,zJH,zO6]
   split_ifs <;> simp
private theorem cKW (y :F) (n:ℕ) (hn:n+1<K1.p) :
  D (ZD D y n)=ZD D y (n+1)*((n:F)+1) := by
 have hf : (n.factorial:F)≠0 :=
  factorial_ne_zero (z12 ao F) (zws hn)
 have hs : (n:F)+1≠0:= by
  rw [← zg0]
  exact natCast_ne_zero (ztH _) hn
 simp only [ZD]
 rw [D.leibniz_div_const _ _ (D.map_natCast _),zs5,zLk,
  zwO,z2R,zg0]
 field_simp [hf,hs]
private def GV (L:ℕ) (x y :F) :F[X] :=
 zcJ x (ahG (M:=L) x (fun j=>ZD D y j.val))
private theorem bnk {L:ℕ} (hL:0<L) (x y :F) (n:ℕ) :
   (GV D L x y).coeff n=if n<L then ZD D y n else 0:= by
 by_cases hn:n<L
 · rw [zYo hn,GV,zWQ]
   exact bG4 x (fun j:Fin L=>ZD D y j.val) ⟨n,hn⟩
 · rw [zNB hn]
   apply zQl
   unfold GV
   rw [zQU]
   exact (bG3 _ _ hL).trans_le (z9m hn)
private theorem dGC {L:ℕ} (hL:0<L) (hp:L<K1.p) (x y :F)
    (hcut: ((D:F→F)^[L]) y=0) :
    GV D L x y∈Oj D:= by
  intro n
  rw [zMD,bnk D hL,bnk D hL]
  by_cases hnext:n+1<L
  · rw [ite_eq_left hnext,ite_eq_left (show n<L by omega)]
    exact cKW D y n (hnext.trans hp)
  · rw [zNB hnext,zero_mul]
    by_cases hn:n<L
    · have he :n+1=L:= by omega
      have hz :ZD D y L=0:= by
        rw [ZD,hcut,zero_div]
      rw [zYo hn,cKW D y n (by rwa [he]),he,hz,zero_mul]
    · rw [zNB hn,zhc]
private theorem gDA (x :F) (hx :D x=1) (H :af 4) (U:F[X])
  (hU:zcJ x U∈Oj D) :
  zcJ x (jW (z12 ao F) H U)∈Oj D:= by
 let t:=(taylorAlgHom x).toRingHom
 let g:=t.comp (zhd (z12 ao F))
 let a :Fin 4→F[X] := fun i=>z75 i.val (zcJ x U)
 have ha (i:Fin 4) :t (z75 i.val U)=a i :=
  (hasseDeriv_taylor U x i.val).symm
 have ht:t (jW (z12 ao F) H U)=zSZ g a H := by
  rw [jW,zUe]
  simp only [ha]
  rfl
 change t (jW (z12 ao F) H U)∈Oj D
 rw [ht]
 let g' : ao[X] →+* Oj D:=g.codRestrict _ (gqv D x hx)
 let a' : Fin 4→Oj D:= fun i=>⟨a i,b5Q D hU i.val⟩
 let P:Oj D:=zSZ g' a' H
 have hm: (P:F[X])=zSZ g a H :=
  zUe H g' (Oj D).subtype a'
 rw [← hm]
 exact P.2
private theorem ctW (H :af 4) {B:ℕ} (hH :tB H B)
   {U:F[X]} (hU:U.natDegree≤133671) :
   (jW (z12 ao F) H U).natDegree≤B:= by
 classical
 rw [jW,MvPolynomial.eval₂_eq]
 apply zMZ
 intro m hm
 have hprod: (∏ i∈m.support,z75 i.val U^m i).natDegree ≤
     m.sum (fun i e=>(133671 - i.val)*e) := by
   unfold Finsupp.sum
   apply (natDegree_prod_le _ _).trans
   apply Finset.sum_le_sum
   intro i _
   change ((z75 i.val U)^m i).natDegree≤(133671 - i.val)*m i
   rw [Nat.mul_comm]
   exact zxc _ ((natDegree_hasseDeriv_le U i.val).trans
     (Nat.sub_le_sub_right hU _))
 exact (zJZ natDegree_map_le hprod).trans (hH m hm)
private theorem gDz (x :F) (H :af 4) (U:F[X]) :
    (jW (z12 ao F) H U).eval x =
      zSZ (zEU x).toRingHom
        (fun i=>(z75 i.val U).eval x) H := by
  change zhy x (zSZ _ _ H)= _
  have hc: (zhy x).comp (zhd (z12 ao F)) =
      (zEU x).toRingHom:= by
    apply z86
    · intro a
      change ((C a).map (z12 ao F)).eval x=zEU x (C a)
      rw [zrL,eval_C,aeval_C]
    · change ((z7y:ao[X]).map (z12 ao F)).eval x =
        zEU x z7y
      rw [zSo,eval_X,zw0]
  rw [zUe,hc]; rfl
private theorem b55 {P:F[X]} (hP:P∈Oj D)
    (h0:P.coeff 0=0) (hdeg:P.natDegree<K1.p) :P=0:= by
  have hz : ∀ n<K1.p,P.coeff n=0:= by
    intro n
    induction n with
    | zero=>exact fun _=>h0
    | succ n ih =>
      intro hn
      have he :=hP n
      rw [zMD,ih (zws hn),zhc] at he
      have hs : (n:F)+1≠0:= by
        rw [← zg0]
        exact natCast_ne_zero (ztH _) hn
      exact (mul_eq_zero.mp he.symm).resolve_right hs
  ext n
  rw [zO6]
  by_cases hn:n<K1.p
  · exact hz n hn
  · exact zQl (hdeg.trans_le (z9m hn))
theorem proof :as6.c2 := by
 intro F _ _ D x y hx hcut H B hH hguard hzero
 let U:=aHA D x y
 change jW (z12 ao F) H U=0
 have hU:U.natDegree<bf :=bG3 _ _ (by decide)
 have hjet (i:Fin 4) : (z75 i.val U).eval x=ZD D y i.val := by
   have h:=bG4 x (fun j=>ZD D y j.val)
     (i.castLE (by decide :4≤bf))
   exact h
 have hroot : (jW (z12 ao F) H U).eval x=0:= by
   rwa [gDz,show (fun i:Fin 4=>(z75 i.val U).eval x) =
     (fun i:Fin 4=>ZD D y i.val) from funext hjet]
 have htranslate :zcJ x U∈Oj D :=
   dGC D (by decide :0<bf) (by decide) x y hcut
 apply (taylor_eq_zero x _).mp
 apply b55 D (gDA D x hx H U htranslate)
 · rwa [zPh]
 · rw [zQU]
   exact (ctW H hH (Nat.le_of_lt_succ hU)).trans_lt
     (lt_of_le_of_lt (z8K B 3) hguard)
end
end cyw
end
section
namespace bzF
noncomputable section
open Polynomial as6
variable {R k F E :Type} [za6 R] [zrb k] [zrb F] [zrb E]
private def Ua (s :R) (e :R →+* F) (h:e s≠0) :zUF s →+* F :=
 ztx s h.isUnit
private theorem be7 (s :R) (e :R →+* F) (h:e s≠0) (a :R) :
  Ua s e h (z12 R (zUF s) a)=e a :=
 zaz s h.isUnit a
private theorem evX (s :R) (e :R →+* F) (h:e s≠0) :
  Ua s e h (zdx s)=(e s)⁻¹:= by
 have heq :=zPw (Ua s e h)
  (IsLocalization.Away.mul_invSelf (S:=zUF s) s)
 rw [zok,be7,map_one] at heq
 exact ((mul_eq_one_iff_inv_eq₀ h).mp heq).symm
private theorem evZ (s :R) (e :R →+* F) (f :R →+* E)
  (he :e s≠0) (hf :f s≠0) (hker : ∀ a,e a=0→f a=0)
  (z :zUF s) (hz :Ua s e he z=0) :Ua s f hf z=0:= by
 obtain ⟨n,a,ha⟩:=IsLocalization.Away.surj s z
 have h₁:=zPw (Ua s e he) ha
 have h₂:=zPw (Ua s f hf) ha
 simp only [zok,zkq,be7,hz,zero_mul] at h₁
 simp only [zok,zkq,be7,hker a h₁.symm] at h₂
 exact (mul_eq_zero.mp h₂).resolve_right (zm1 _ hf)
private def aot {M:ℕ} (c:k →+* R) (s x :R) (a :Fin M→R) :
  (zUF s)[X] :=
 let η:=z12 R (zUF s)
 ahG (η x) (fun i:Fin M=>η (a i) *
  (zdx s)^(2*i.val)*η (c (i.val.factorial:k)⁻¹))
def bdU {M:ℕ} (e :R →+* F) (s x :R) (a :Fin M→R) :F[X] :=
 ahG (e x) (fun i:Fin M=>e (a i)/e s^(2*i.val)/(i.val.factorial:F))
private theorem ey5 {M:ℕ} (c:k →+* R) (s x :R) (a :Fin M→R)
  (e :R →+* F) (he :e s≠0) :
  (aot c s x a).map (Ua s e he)=bdU e s x a := by
 unfold aot bdU
 rw [cZs,be7]
 apply zPw (ahG (M:=M) (e x))
 funext i
 have hc:e (c (i.val.factorial:k)⁻¹)=(i.val.factorial:F)⁻¹:= by
  change (e.comp c) _ = _
  rw [map_inv₀,zGu]
 simp only [zok,zkq,be7,evX,hc,div_eq_mul_inv,inv_pow]
private def bcw {M:ℕ} {B:Type} [za6 B] (c:k →+* B) (U:B[X])
  (q:z3y (Fin M) k) :B :=
 q.eval₂ c (fun i=>U.coeff i.val)
private theorem map_equation {M:ℕ} {B:Type} [za6 B] (h:B →+* F)
  (c:k →+* B) (U:B[X]) (q:z3y (Fin M) k) :
  h (bcw c U q)=bcw (h.comp c) (U.map h) q:= by
 simp only [bcw,zUe,coeff_map]
private theorem de7 {M:ℕ} (c:k →+* R) (s x :R) (a :Fin M→R)
   (e :R →+* F) (he :e s≠0) (q:z3y (Fin M) k) :
   Ua s e he (bcw ((z12 R (zUF s)).comp c)
     (aot c s x a) q)=bcw (e.comp c) (bdU e s x a) q:= by
 rw [map_equation,ey5]
 have hc: (Ua s e he).comp ((z12 R (zUF s)).comp c)=e.comp c :=
   zz4 fun b=>be7 s e he (c b)
 rw [hc]
theorem transport {M:ℕ} (c:k →+* R) (s x :R) (a :Fin M→R)
  (e :R →+* F) (f :R →+* E) (he :e s≠0) (hf :f s≠0)
  (hker : ∀ b,e b=0→f b=0) (q:z3y (Fin M) k)
  (hq:q.eval₂ (e.comp c) (fun i=>(bdU e s x a).coeff i.val)=0) :
  q.eval₂ (f.comp c) (fun i=>(bdU f s x a).coeff i.val)=0:= by
 change bcw (f.comp c) _ q=0
 rw [← de7 c s x a f hf q]
 apply evZ s e f he hf hker
 rw [de7]
 exact hq
end
end bzF
end
section
set_option maxRecDepth 1600
set_option maxHeartbeats 500000
namespace bzF
noncomputable section
open Polynomial aR dN rW as6
private def btz :ao →+* af 4 :=MvPolynomial.C.comp z1z
private def aow (S:ao[X]) :af 4 →+* GeoField :=
 j8.comp (zY9 (jet S))
private theorem b8L (S:ao[X]) (H :af 4) :
 aow S H=j8 (cK H S) :=rfl
private theorem ezw (S:ao[X]) :
  (aow S).comp btz=ni:= by
 apply zz4
 intro a
 simp only [aow,btz,zQb,z9X,ni]
private theorem dOw (P:n8) :
  (Zx P).comp btz=CX P:= by
 apply zz4
 intro a
 simp only [Zx,btz,CX,ni,
  zQb,zpw]
private theorem eft:zq4 j8 :=
 (z12 lN GeoField).injective.comp (zxb ao[X] lN)
private theorem dXo (g:af 4) (S:ao[X]) (hg:cK g S=0)
   (hs :aow S (zai g)≠0) (i:Fin bf) :
   aow S (su g i.val)/aow S (zai g)^(2*i.val) /
     (i.val.factorial:GeoField)=j8 (z75 i.val S) := by
 have ho:zst^[i.val] S=(i.val.factorial:ao[X])*z75 i.val S:= by
   have h:=congrFun (z6T (R:=ao) (k :=i.val)) S
   change i.val.factorial•z75 i.val S=zst^[i.val] S at h
   simpa only [zVT] using h.symm
 have hfact :=factorial_ne_zero ni (i.isLt.trans (by decide :bf<K1.p))
 rw [b8L S (su g i.val),arh _ _ hg,zok,zkq,
   ← b8L,zE5 _ (zm1 _ hs),ho,zok,zGu,
   zE5 _ hfact]
private theorem d2n (U:ao[X]) :
  (U.map ni).eval rI=j8 U:= by
 change ((zhy rI).comp (zhd ni)) U= _
 apply zLs
 apply z86 <;> simp [ni,rI]
private theorem recover {B:Type} [za6 B] {M:ℕ} (x :B) (a :Fin M→B)
   (U:B[X]) (hU:U.natDegree<M)
   (ha : ∀ i:Fin M,a i=(z75 i.val U).eval x) :ahG x a=U:= by
 apply taylor_injective x
 ext n
 by_cases hn:n<M
 · rw [zWQ,zWQ]
   exact (bG4 x a ⟨n,hn⟩).trans (ha ⟨n,hn⟩)
 · have hM:0<M:=(zD0 _).trans_lt hU
   have hleft:=(bG3 x a hM).trans_le (z9m hn)
   have hright:=hU.trans_le (z9m hn)
   rw [zQl ((zQU _ _).trans_lt hleft),
     zQl ((zQU _ _).trans_lt hright)]
private theorem ezA (g:af 4) (S:ao[X]) (hg:cK g S=0)
  (hs :aow S (zai g)≠0) (hd:S.natDegree<bf) :
  ab2 (aow S) g=S.map ni:= by
 have hx :KK (aow S)=rI:= by
  simp only [KK,aow,zQb,z9X,rI]
 unfold ab2
 rw [hx]
 apply recover _ _ _ (natDegree_map_le.trans_lt hd)
 intro i
 rw [dXo g S hg hs i,zvb,d2n]
private theorem ear {F:Type} [zrb F] (e :af 4 →+* F) (g:af 4) :
 bdU e (zai g) (znf z7y)
  (fun i:Fin bf=>su g i.val)=ab2 e g:=rfl
private def aiq {F:Type} [zrb F] (k :ao →+* F) (U:F[X]) (q:jo) :Prop :=
 q.eval₂ k (fun i=>U.coeff i.val)=0
private theorem ez6 {F:Type} [zrb F] (k :ao →+* F) (U:F[X])
 (q:jo) :q∈Zv k U↔aiq k U q:=Iff.rfl
private theorem ezz {F:Type} [zrb F] (k :ao →+* F) (S:ao[X]) (q:jo)
  (h:aiq k (S.map k) q) :zY9 (Gp S) q=0:= by
 unfold aiq at h
 simp only [coeff_map] at h
 apply (zVB _ k.injective).mp
 rw [z6r]
 exact h
private theorem gDZ (P:n8) [P.IsPrime] (g:af 4) (S:ao[X])
  (hgen:Zx P (zai g)≠0) (hmark :aow S (zai g)≠0)
  (hP:P≤Ch S) (q:jo)
  (hq:aiq (CX P) (ab2 (Zx P) g) q) :
  aiq ni (ab2 (aow S) g) q:= by
 have hker (b:af 4) (hb:Zx P b=0) :aow S b=0:= by
  have hz :=BO.Ue.mp (hP ((bYq P b).mp hb))
  rw [b8L,hz,zhc]
 rw [← dOw] at hq
 rw [← ezw S]
 rw [← ear] at hq ⊢
 unfold aiq at hq ⊢
 exact transport (k :=ao) (R:=af 4) (F:=tJ P) (E :=GeoField) (M:=bf)
  btz (zai g) (znf z7y)
  (fun i:Fin bf=>su g i.val) (Zx P) (aow S)
  hgen hmark hker q hq
theorem proof :as6.c3:= by
 intro g P hp hg hsep S hd hP hr
 have hgen:Zx P (zai g)≠0:= fun h=>hsep ((bYq P _).mp h)
 have hmark :aow S (zai g)≠0:=(zw1 _ eft).mpr hr
 have hzero :=BO.Ue.mp (hP hg)
 apply MvPolynomial.mem_zeroLocus_iff.mpr
 intro q hq
 rw [ez6] at hq
 have h:=gDZ P g S hgen hmark hP q hq
 rw [ezA g S hzero hmark hd] at h
 exact ezz ni S q h
end
end bzF
end
section
namespace Qr
noncomputable section
open cu gT Polynomial
abbrev zH :=AlgebraicClosure aQ
def aQQ:aZ →+* zH :=
 (z12 aQ zH).comp (z12 aZ aQ)
def aaU (y v :zH) :z87 →+* zH :=
  zOD (z12 FX zH)
    ![z12 aQ zH (ek 0),
      z12 aQ zH (ek 1),y,v]
def PW (a b:zH) :z87 →+* zH :=
  zOD (z12 FX zH)
    ![a,b,z12 aQ zH (ek 0),
      z12 aQ zH (ek 1)]
def aF5 (I:znc z87) (y v :zH) :Prop :=
 zdq (aaU y v)=I
def bAH (I:znc z87) :Prop :=
  ∃ a b,zdq (PW a b)=I ∧
    zR6 aQ a∧zR6 aQ b
def bQ5 (I:znc z87) (P:Jet) (m:ℕ) :Prop :=
  ∀ a b:ℕ,a+b< m →
    iJ (A5 0 a (A5 1 b P))∈I
def aUO (P:Jet) :zM1 (zM1 zH) :=
 P.map (zhd aQQ)
def cxB (P:Jet) (y v :zH) (m:ℕ) :Prop :=
  ∀ a b:ℕ,a+b< m →
    (z75 a ((z75 b (aUO P)).eval (C v))).eval y=0
end
end Qr
end
section
set_option maxHeartbeats 1000000
namespace Qr
noncomputable section
open cu gT Polynomial
open scoped BigOperators nonZeroDivisors
end
end Qr
end
section
namespace Qr
noncomputable section
open K1 cu gT Polynomial
def c2 :Prop :=
  ∀ (I:znc z87),bAH I →
    ∀ (P:Jet) (m:ℕ),m<p→bQ5 I P m →
    ∀ y v,aF5 I y v→cxB P y v m
end
end Qr
end
section
namespace dnm
noncomputable section
open K1 cu gT Qr
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Sw:=z3y (Fin 2) aZ
private def bCx (e :Fin 4 ≃ Fin 2 ⊕ Fin 2) :z87 ≃+* Sw :=
 ((zGY FX e).trans
   (z3k FX (Fin 2) (Fin 2))).toRingEquiv
private abbrev aki:Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
 finSumFinEquiv.symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
private abbrev aOh:Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
 (finSumFinEquiv (m:=2) (n:=2)).symm
private theorem qR (e :Fin 4 ≃ Fin 2 ⊕ Fin 2) :
    (z12 Sw vR).comp (bCx e).toRingHom =
      zOD (MvPolynomial.C.comp (z12 FX aQ))
        (Sum.elim z9v (fun i=>znf (ek i)) ∘ e) := by
  apply zXT
  · intro c
    simp [bCx]
    rfl
  · intro i
    rw [zQb,zrD,z3s]
    change z12 Sw vR
      (z3k FX (Fin 2) (Fin 2)
        (zGY FX e (z9v i)))= _
    rw [MvPolynomial.renameEquiv_apply,z6l,zu8]
    cases e i <;> simp [ek]
private theorem pO:Dk =
   (z12 Sw vR).comp (bCx aki).toRingHom:= by
 rw [qR]
 apply zXT
 · intro c
   simp only [Dk,zTv]
 · intro i
   simp only [Dk,zrD,z3s]
   fin_cases i <;> rfl
private theorem JH :CG =
   (z12 Sw vR).comp (bCx aOh).toRingHom:= by
 rw [qR]
 apply zXT
 · intro c
   simp only [CG,zTv]
 · intro i
   simp only [CG,zrD,z3s]
   fin_cases i <;> rfl
private theorem cpe (E :Type) [zrb E] [zZE aQ E]
  [zAa aQ E] (hsize :zsE aQ E<p) (x :E) :
  IsSeparable aQ x := by
 let:CharP aQ p:=zgG
  ((z12 FX aQ).comp jz).injective p
 have hx :IsIntegral aQ x :=zmn x
 let f :=minpoly aQ x
 have hpos :0<f.natDegree :=minpoly.natDegree_pos hx
 have hlt:f.natDegree<p:=(minpoly.natDegree_le x).trans_lt hsize
 have hcast: (f.natDegree :aQ)≠0:= by
  intro h
  exact (ziF hlt) (zTm hpos ((zX2 aQ p _).mp h))
 change f.Separable
 apply (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hx)).2
 intro hzero
 obtain ⟨n,hn⟩:=zwS hpos.ne'
 apply hcast
 have hcoeff :=zPw (fun q:zM1 aQ=>q.coeff n) hzero
 change f.derivative.coeff n=(0:zM1 aQ).coeff n at hcoeff
 have hmonic:f.coeff f.natDegree=1 :=(minpoly.monic hx).leadingCoeff
 rw [hn] at hmonic
 rw [zMD,zO6,← zg0,
  ← hn,hmonic,one_mul] at hcoeff
 exact hcoeff
private theorem b2Y (g:z87 →+* vR) (e :z87 ≃+* Sw)
   (hg:g=(z12 Sw vR).comp e.toRingHom)
   (I:znc z87) (hI:I.IsPrime) [zAa aQ (vR ⧸ I.map g)]
   (hpos :0<zsE aQ (vR ⧸ I.map g))
   (hsize :zsE aQ (vR ⧸ I.map g)<p) :
   ∃ f :vR →ₐ[aQ] zH,
     zdq (f.toRingHom.comp g)=I ∧ ∀ x,zR6 aQ (f x) := by
 let S:Submonoid Sw:=(zgt aZ).map znf
 let J:znc vR:=I.map g
 let I' : znc Sw:=I.map e.toRingHom
 have hJ:J=I'.map (z12 Sw vR) := by
   rw [z0L,← hg]
 have hI' : I'.IsPrime := by
   change (I.map (e :z87 →+* Sw)).IsPrime
   rw [Ideal.map_comap_of_equiv e]
   exact hI.comap _
 have hproper :J ≠ ⊤ := by
   intro ht
   let:Subsingleton (vR ⧸ J) :=Ideal.Quotient.subsingleton_iff.mpr ht
   exact hpos.ne' (z6g aQ (vR ⧸ J))
 have hd:Disjoint (S:Set Sw) (I' : Set Sw) :=
   (IsLocalization.map_algebraMap_ne_top_iff_disjoint S vR I').mp (hJ ▸ hproper)
 have hcontract : (I'.map (z12 Sw vR)).comap
     (z12 Sw vR)=I' :=
   ztT S vR hI' hd
 let:J.IsPrime :=hJ ▸ znL S vR I' hI' hd
 let:zrb (vR ⧸ J) :=fieldOfFiniteDimensional aQ _
 let:Module.IsTorsionFree aQ (vR ⧸ J) :=
   DivisionSemiring.to_moduleIsTorsionFree
 let emb: (vR ⧸ J) →ₐ[aQ] zH :=IsAlgClosed.lift
 refine ⟨emb.comp (zvR aQ J),?_,?_⟩
 · change zdq (emb.toRingHom.comp ((zVv J).comp g))=I
   rw [zGm _ emb.injective,← zEW,Ideal.mk_ker,
     hg,← Ideal.comap_comap,hJ,hcontract]
   exact zFA _ e.bijective
 · intro x
   exact (cpe (vR ⧸ J) hsize (zVv J x)).map
     emb emb.injective
private theorem dcQ (f :vR →ₐ[aQ] zH) :
   aaU (f (z9v 0)) (f (z9v 1)) =
    f.toRingHom.comp Dk := by
 apply zXT
 · intro c
   simp only [aaU,Dk,zTv,zQb]
   change z12 FX zH c =
    f (z12 aQ vR (z12 FX aQ c))
   rw [f.commutes,← zG3 FX aQ zH]
 · intro i
   fin_cases i <;> simp [aaU,Dk,← zKm]
private theorem zq (f :vR →ₐ[aQ] zH) :
   PW (f (z9v 0)) (f (z9v 1)) =
    f.toRingHom.comp CG:= by
 apply zXT
 · intro c
   simp only [PW,CG,zTv,zQb]
   change z12 FX zH c =
    f (z12 aQ vR (z12 FX aQ c))
   rw [f.commutes,← zG3 FX aQ zH]
 · intro i
   fin_cases i <;> simp [PW,CG,← zKm]
end
end dnm
end
section
namespace aZb
noncomputable section
open cu gT Qr
open scoped BigOperators nonZeroDivisors
private abbrev Dual:=TrivSqZeroExt zH zH
private def a1w (j:Fin 2) :aZ →+* Dual :=
 zOD
  ((TrivSqZeroExt.inlHom zH zH).comp (z12 FX zH))
  (fun i=>⟨z12 aQ zH (ek i),if i=j then 1 else 0⟩)
private abbrev residue :Dual →+* zH :=
 (zx5 zH zH zH).toRingHom
private theorem cCZ (j:Fin 2) (x :FX) :
  a1w j (znf x)=zx4 (z12 FX zH x) :=
 zTv _ _ _
private theorem cC0 (i j:Fin 2) :
  a1w j (z9v i) =
   ⟨z12 aQ zH (ek i),if i=j then 1 else 0⟩ :=
 zrD _ _ _
private theorem c8y (j:Fin 2) :
   residue.comp (a1w j)=aQQ:= by
 apply zXT
 · intro x
   rw [zQb,cCZ]
   change z12 FX zH x =
    z12 aQ zH (z12 aZ aQ (z12 FX aZ x))
   exact (zG3 FX aZ zH x).trans
    (zG3 aZ aQ zH _)
 · intro i
   rw [zQb,cC0]
   rfl
private theorem cC1 (j:Fin 2) (s :aZ⁰) :zWB (a1w j s) := by
 apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
 apply isUnit_iff_ne_zero.mpr
 change residue (a1w j s)≠0
 rw [← zQb,c8y]
 have hi:zq4 aQQ :=
  (z12 aQ zH).injective.comp (zxb aZ aQ)
 intro hz
 exact zyw s.property (hi (hz.trans (zhc aQQ).symm))
private def aMg (j:Fin 2) :aQ →+* Dual :=
 zvq (cC1 j)
private theorem fWO (j:Fin 2) :
  residue.comp (aMg j)=z12 aQ zH := by
 apply zuW aZ⁰
 apply zz4
 intro s
 simp only [zQb,aMg,zX4]
 change residue (a1w j s)=aQQ s
 exact zmU (c8y j) s
private theorem dyC (j:Fin 2) (x :FX) :
   aMg j (z12 FX aQ x) =
     zx4 (z12 FX zH x) := by
 rw [zG3 FX aZ aQ,aMg,zX4]
 exact cCZ j x
private theorem cCY (i j:Fin 2) :
   aMg j (ek i) =
     ⟨z12 aQ zH (ek i),if i=j then 1 else 0⟩:= by
 rw [show aMg j (ek i)=a1w j (z9v i) from
   zX4 (cC1 j) _]
 exact cC0 i j
private theorem ev3 (a b:zH)
   (ha :zR6 aQ a) (hb:zR6 aQ b) (j:Fin 2) :
   ∃ e :z87 →+* Dual,residue.comp e=PW a b ∧
     (∀ x,e (znf x)=zx4 (z12 FX zH x)) ∧
     (e (z9v 2)).snd=(if j=0 then 1 else 0) ∧
     (e (z9v 3)).snd=(if j=1 then 1 else 0) ∧
     zdq (PW a b)≤zdq e := by
 let E :=separableClosure aQ zH
 let a' : E :=⟨a,ha⟩
 let b' : E :=⟨b,hb⟩
 let:zZE aQ Dual:=(aMg j).toAlgebra
 let red:Dual →ₐ[aQ] zH :=
   { residue with commutes' := fun x=>zmU (fWO j) x }
 have hred:zpX red:= fun x=>⟨zx4 x,rfl⟩
 have hnil:IsNilpotent (zdq red.toRingHom) :=
   ⟨2,TrivSqZeroExt.kerIdeal_sq zH zH⟩
 let:Algebra.FormallyEtale aQ E :=Algebra.FormallyEtale.of_isSeparable _ _
 let ext:E →ₐ[aQ] Dual :=
   Algebra.FormallySmooth.liftOfSurjective E.val red hred hnil
 have hext (x :E) :residue (ext x)=E.val x :=
   Algebra.FormallySmooth.liftOfSurjective_apply E.val red hred hnil x
 let point :z87 →+* E :=
   zOD (z12 FX E)
     ![a',b',z12 aQ E (ek 0),z12 aQ E (ek 1)]
 have hpoint :E.val.toRingHom.comp point=PW a b:= by
   apply zXT
   · intro x
     simp [point,PW]
   · intro i
     fin_cases i <;> simp [point,PW,a',b']
 refine ⟨ext.toRingHom.comp point,?_,?_,?_,?_,?_⟩
 · apply zz4
   intro Q
   exact (hext (point Q)).trans (zmU hpoint Q)
 · intro x
   change ext (point (znf x))= _
   rw [show point (znf x)=z12 FX E x from zTv ..,
     zG3 FX aQ E,zKk]
   exact dyC j x
 · change (ext (point (z9v 2))).snd= _
   rw [show point (MvPolynomial.X 2)=algebraMap aQ E (ek 0) by simp [point],
     zKk]
   change (aMg j (ek 0)).snd= _
   rw [cCY]
   simp [eq_comm]
 · change (ext (point (z9v 3))).snd= _
   rw [show point (MvPolynomial.X 3)=algebraMap aQ E (ek 1) by simp [point],
     zKk]
   change (aMg j (ek 1)).snd= _
   rw [cCY]
   simp [eq_comm]
 · intro Q hQ
   rw [zry] at hQ ⊢
   have hp:E.val (point Q)=0:=(zmU hpoint Q).trans hQ
   change ext (point Q)=0
   rw [E.val.injective (hp.trans (zhc E.val).symm),zhc]
private theorem chain (e :z87 →+* Dual) (g:z87 →+* zH)
    (hg:residue.comp e=g)
    (hc : ∀ x,e (znf x)=zx4 (z12 FX zH x))
    (Q:z87) :
    (e Q).snd = ∑ i:Fin 4,g (zWe i Q)*(e (z9v i)).snd:= by
  have hf (P:z87) : (e P).fst=g P:=zmU hg P
  induction Q using z5i with
  | C x=>simp [hc]
  | add P Q hP hQ=>simp [hP,hQ,add_mul,Finset.sum_add_distrib]
  | mul_X P j hP =>
      simp only [zok,TrivSqZeroExt.snd_mul,hf,hP,zs5,
        MulOpposite.smul_eq_mul_unop,MulOpposite.unop_op,zGW,
        zrl,add_mul,zfW,← zxw,ztg]
      have hs : (∑ i:Fin 4,
          g (zWe i (z9v j))*(e (z9v i)).snd) =
          (e (z9v j)).snd:= by
        rw [zi6 j]
        · simp
        · intro i _ hij
          simp [zVY hij.symm]
        · simp
      rw [hs]
      rw [zV7]
      congr 1
      rw [Finset.sum_mul]
      apply zUo rfl
      intro i _
      ring
theorem gAn {I:znc z87} (hI:bAH I)
    {Q:z87} (hQ:Q∈I) (h0:zWe 0 Q∈I)
    (h1 :zWe 1 Q∈I) :
    zWe 2 Q∈I∧zWe 3 Q∈I:= by
  obtain ⟨a,b,hker,ha,hb⟩:=hI
  subst I
  let g:=PW a b
  have hzero (j:Fin 2) :
      (if j=0 then g (zWe 2 Q) else 0) +
        (if j=1 then g (zWe 3 Q) else 0)=0:= by
    obtain ⟨e,he,hC,h2,h3,hker⟩:=ev3 a b ha hb j
    have key :=chain e g he hC Q
    rw [RingHom.mem_ker.mp (hker hQ)] at key
    rw [Fin.sum_univ_four] at key
    rw [RingHom.mem_ker.mp h0,RingHom.mem_ker.mp h1,h2,h3] at key
    fin_cases j <;> simpa using key.symm
  exact ⟨RingHom.mem_ker.mpr (by simpa using hzero 0),
    RingHom.mem_ker.mpr (by simpa using hzero 1)⟩
end
end aZb
end
section
namespace aZb
noncomputable section
open K1 cu gT Qr Polynomial
abbrev ER (i:Fin 4) :z87→Ambient:=zWe i
private theorem derivative_eval {R:Type*} [za6 R]
   (f :z87 →+* R[X]) (i:Fin 4)
   (hC : ∀ x,zst (f (znf x))=0)
   (hX : ∀ j,zst (f (z9v j))=f (ER i (z9v j))) :
   zEB f (ER i) derivative := by
 intro Q
 induction Q using z5i with
 | C x=>simp [ER,hC]
 | add P Q hP hQ =>
   simpa only [ER,zrl,derivative_add] using congrArg₂ (· + ·) hP hQ
 | mul_X P j hP =>
   simp only [ER,zGW,zrl,zok,zAg,hP,hX]
private def aAh (i:Fin 2) :Fin 4 :=zQY (by decide) i
private def translation (i:Fin 4) :z87 →+* z87[X] :=
 zOD (C.comp znf)
  (fun j=>C (z9v j:z87)+if j=i then z7y (R:=z87) else 0)
private theorem gDY (i:Fin 4) (Q:z87) :
   (translation i Q).coeff 0= Q:= by
 have h: (zhy (0:z87)).comp (translation i)=zz5 Ambient:= by
   apply zXT
   · simp [translation]
   · intro j
     by_cases hj:j=i <;> simp [translation,hj]
 rw [coeff_zero_eq_eval_zero]
 exact zmU h Q
private theorem gDU (i:Fin 4) :
   zEB (translation i) (ER i) derivative := by
 apply derivative_eval
 · simp [translation]
 · intro j
   by_cases h:j=i <;> simp [translation,ER,h]
private def AH :aZ →+* Ambient:=oi.comp pZ
private theorem bu8 (k :Fin 3) :
  oi (z9v k)=z9v (zQY (by decide) k) := by
 simp [oi]
private theorem gBP (P:Jet) :
  iJ P=P.sum fun j g =>
   (g.sum fun k c=>AH c*z9v 2^k)*z9v 3^j:= by
 simp only [iJ,A7,z4Q,eval₂_eq_sum,zQb,
  Polynomial.sum,zdo,zok,zkq,AH,bu8]
 rfl
private theorem gDW (i:Fin 2) (c:aZ) :
    translation (aAh i) (AH c)=(Vy i c).map AH := by
  have h: (translation (aAh i)).comp AH =
      (zhd AH).comp (Vy i) := by
    apply zXT
    · simp [translation,Vy,AH,oi,pZ]
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [translation,Vy,AH,oi,pZ,aAh]
  exact zmU h c
private theorem gDX (i:Fin 2) (r :ℕ) (P:Jet) :
    (translation (aAh i) (iJ P)).coeff r=iJ (A5 i r P) := by
  have hY:translation (aAh i) (z9v 2)=C (z9v 2) := by
    fin_cases i <;> simp [translation,aAh]
  have hV:translation (aAh i) (z9v 3)=C (z9v 3) := by
    fin_cases i <;> simp [translation,aAh]
  have hYpow (k :ℕ) :
      translation (aAh i) (z9v 2^k)=C (z9v 2^k) := by
    rw [zkq,hY,← C_pow]
  have hVpow (j:ℕ) :
      translation (aAh i) (z9v 3^j)=C (z9v 3^j) := by
    rw [zkq,hV,← C_pow]
  have hm (j k :ℕ) (c:aZ) :
      iJ (monomial j (monomial k c))=AH c*z9v 2^k *
        z9v 3^j:= by
    simp [iJ,A7,eval₂_monomial,AH,bu8]
  conv_lhs=>rw [gBP]
  simp only [A5,Polynomial.sum,zdo,zok,hm,hYpow,hVpow,
    zaW,coeff_mul_C,gDW,coeff_map,Finset.sum_mul]
theorem bNJ (i:Fin 2) (r :ℕ) (P:Jet) :
  (ER (aAh i))^[r] (iJ P)=r.factorial•iJ (A5 i r P) := by
 have h:=(gDU (aAh i)).iterate_right r (iJ P)
 have hc:=zPw (fun Q:z87[X]=>Q.coeff 0) h
 simpa only [gDY,coeff_iterate_derivative,zbc,
  Nat.descFactorial_self,gDX] using hc
private def aRg (v :zH) :z87 →+* zH[X] :=
 zOD (C.comp (z12 FX zH))
  ![C (z12 aQ zH (ek 0)),
    C (z12 aQ zH (ek 1)),z7y,C v]
private def amS:z87 →+* zM1 (zM1 zH) :=
 zOD (C.comp (C.comp (z12 FX zH)))
  ![C (C (z12 aQ zH (ek 0))),
    C (C (z12 aQ zH (ek 1))),C (z7y (R:=zH)),z7y]
private theorem gM7 (v :zH) :
   zEB (aRg v) (ER 2) derivative := by
 apply derivative_eval
 · simp [aRg]
 · intro j
   fin_cases j <;> simp [aRg,ER,zYE]
private theorem gKD :
   zEB amS (ER 3) derivative := by
 apply derivative_eval
 · simp [amS]
 · intro j
   fin_cases j <;> simp [amS,ER,zYE]
private theorem d3h (y v :zH) :
   (zhy y).comp (aRg v)=aaU y v := by
 apply zXT
 · simp [aRg,aaU]
 · intro j
   fin_cases j <;> simp [aRg,aaU]
private theorem d3g (v :zH) :
   (zhy (C v)).comp amS=aRg v := by
 apply zXT
 · simp [aRg,amS]
 · intro j
   fin_cases j <;> simp [aRg,amS]
private theorem gKE (P:Jet) :amS (iJ P)=aUO P:= by
  have hs :amS.comp AH=C.comp (C.comp aQQ) := by
    apply zXT
    · intro x
      simp [amS,AH,oi,pZ,aQQ,
        ← zG3]
      exact zG3 FX aZ zH x
    · intro j
      fin_cases j <;> simp [amS,AH,oi,pZ,aQQ,ek]
  have hy :amS.comp (oi.comp A7)=C.comp (zhd aQQ) := by
    apply z86
    · intro c
      change amS (oi (A7 (C c)))= _
      simpa [A7,AH] using zmU hs c
    · simp [A7,amS,bu8]
  change amS (P.eval₂ (oi.comp A7) (z9v 3))= _
  rw [zly,hy,show amS (z9v 3)=z7y by simp [amS]]
  rfl
theorem d2x (P:Jet) (a b:ℕ) (y v :zH) :
    aaU y v ((ER 2)^[a] ((ER 3)^[b] (iJ P))) =
      a.factorial•b.factorial •
        (z75 a ((z75 b (aUO P)).eval (C v))).eval y := by
  rw [← d3h,zQb,
    (gM7 v).iterate_right a,
    ← d3g,zQb,
    gKD.iterate_right b,gKE]
  rw [← z6T,← z6T]
  simp only [LinearMap.coe_smul,Pi.smul_apply,map_nsmul,coe_evalRingHom]
  exact smul_comm _ _ _
end
end aZb
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace baD
noncomputable section
open cu qQ gT Polynomial
local notation "SF" => qQ.aQ
private def adO:aZ ≃+* IW :=
 ((zGY FX (zFe (0:Fin 2) 1)).trans
   (z8s FX 1)).toRingEquiv.trans
   (Polynomial.mapEquiv (zpe FX (Fin 1)).toRingEquiv)
private theorem epA (x :FX) :
  adO (znf x)=C (C x) := by
 change (z8s FX 1
  (zHw (zFe (0:Fin 2) 1) (znf x))).map
    (zpe FX (Fin 1)).toRingHom= _
 simp [zyf]
private theorem epB :
   adO (z9v 0)=C (z7y (R:=FX)) := by
 change (z8s FX 1
   (zHw (zFe (0:Fin 2) 1) (z9v 0))).map
     (zpe FX (Fin 1)).toRingHom= _
 rw [z6l,Equiv.swap_apply_left]
 rw [show (1 :Fin 2)=(0:Fin 1).succ from rfl,z07]
 simp
private theorem epC :
   adO (z9v 1)=Polynomial.X:= by
 change (z8s FX 1
   (zHw (zFe (0:Fin 2) 1) (z9v 1))).map
     (zpe FX (Fin 1)).toRingHom= _
 rw [z6l,Equiv.swap_apply_right,zOO,zSo]
private def a4i:tJ ≃+* SF :=
 IsFractionRing.ringEquivOfRingEquiv (A:=IW) (K:=tJ)
  (B:=aZ) (L:=SF) adO.symm
private abbrev ctw:=z12 IW tJ
private abbrev gBW:aZ →+* SF:=z12 aZ SF
private theorem edL (x :IW) :
  a4i (ctw x)=gBW (adO.symm x) :=
 IsFractionRing.ringEquivOfRingEquiv_algebraMap (A:=IW) (K:=tJ)
  (B:=aZ) (L:=SF) adO.symm x
set_option backward.isDefEq.respectTransparency true
private theorem cV1 {T:Type*} [CommSemiring T] {g h:Jet →+* T}
  (hc : ∀ x :FX,g (C (C (znf x)))=h (C (C (znf x))))
  (hs : ∀ i:Fin 2,g (C (C (z9v i)))=h (C (C (z9v i))))
  (hy :g (C (z7y (R:=aZ)))=h (C (z7y (R:=aZ))))
  (hv :g z7y=h z7y) :g=h:= by
 apply z3l _ hv
 apply z3l _ hy
 exact zXT (fun x=>hc x) (fun i=>hs i)
@[simp] private theorem cty (x :FX) :
   iJ (C (C (znf x)))=znf x := by
  simp [iJ,A7,oi,pZ]
@[simp] private theorem aJQ (i:Fin 2) :
   iJ (C (C (z9v i)))=z9v (zQY (by decide) i) := by
  fin_cases i <;> simp [iJ,A7,oi,pZ]
@[simp] private theorem ctD :
   iJ (C (z7y (R:=aZ)))=z9v 2 := by
  simp [iJ,A7,oi]
@[simp] private theorem ctC :
   iJ (z7y (R:=zS3))=z9v 3:= by
  simp [iJ]
private theorem gBQ:zpX iJ:= by
 intro Q
 induction Q using z5i with
 | C x=>exact ⟨C (C (MvPolynomial.C x)),cty x⟩
 | add P Q hP hQ =>
   obtain ⟨P',rfl⟩:=hP
   obtain ⟨Q',rfl⟩:=hQ
   exact ⟨P' + Q',zrl _ _ _⟩
 | mul_X P i hP =>
   obtain ⟨P',rfl⟩:=hP
   have hX : ∃ j,iJ j=z9v i:= by
     fin_cases i
     · exact ⟨_,aJQ 0⟩
     · exact ⟨_,aJQ 1⟩
     · exact ⟨_,ctD⟩
     · exact ⟨_,ctC⟩
   obtain ⟨j,hj⟩:=hX
   exact ⟨P' * j,by rw [zok,hj]⟩
private theorem bNC (x :FX) :
  aif (znf x)=z12 FX HR x := by
 change z12 SF HR (z12 aZ SF (z12 FX aZ x))= _
 rw [← zG3 aZ SF HR,
  ← zG3 FX aZ HR]
private theorem co4 (y v :HR) :
   (Qr.aaU y v).comp iJ=aXz y v := by
 apply cV1
 · intro x
   simp [Qr.aaU,aXz,bNC]
 · intro i
   fin_cases i <;>
     simp [Qr.aaU,aXz,aif,z9Y]
 · simp [Qr.aaU,aXz]
 · simp [Qr.aaU,aXz]
theorem ddb {q:zI} {y v :HR} (h:aF5 q y v) :
  (zdq (Qr.aaU y v)).comap iJ=q.asIdeal:= by
 rw [zEW,co4,h]
private theorem b4B (x :FX) :adO.symm (C (C x))=znf x :=
 adO.symm_apply_eq.mpr (epA x).symm
private theorem b4D:adO.symm (C (z7y (R:=FX)))=z9v 0 :=
 adO.symm_apply_eq.mpr epB.symm
private theorem b4C:adO.symm (z7y (R:=zM1 FX)) =
  z9v 1 :=
 adO.symm_apply_eq.mpr epC.symm
theorem ep4 {q:zI} (h:N5 q) {y v :HR}
    (hyv :aF5 q y v) :
    Qr.bAH (zdq (Qr.aaU y v)) := by
  obtain ⟨g,hg,hker,hsep⟩:=h.jet_side
  let:zZE tJ SF:=a4i.toRingHom.toAlgebra
  let l:aiF →ₐ[tJ] HR :=
    IsAlgClosed.lift (R:=tJ) (S:=aiF) (M:=HR)
  let a (i:Fin 2) :=l (g (C (C (z9v i))))
  have hmap (x :IW) :
      l (g (Ng x))=aif (adO.symm x) := by
    rw [show g (Ng x)=bHX x from zmU hg x]
    change l (z12 tJ aiF (ctw x))= _
    rw [l.commutes,zG3 tJ SF HR]
    change z12 SF HR (a4i (ctw x))= _
    exact zPw (z12 SF HR) (edL x)
  have hchart: (Qr.PW (a 0) (a 1)).comp iJ =
      l.toRingHom.comp g:= by
    apply cV1
    · intro x
      simpa [Qr.PW,Ng,b4B,bNC] using
        (hmap (C (C x))).symm
    · intro i
      fin_cases i <;> simp [Qr.PW,a]
    · simpa [Qr.PW,Ng,b4D,
        aif,z9Y] using
        (hmap (C (z7y (R:=FX)))).symm
    · simpa [Qr.PW,Ng,b4C,
        aif,z9Y] using
        (hmap (z7y (R:=zM1 FX))).symm
  have hsep' (x :aiF) (hx :zR6 tJ x) :zR6 SF (l x) := by
    have hx' : (minpoly tJ x).Separable :=hx
    apply (hx'.map (f :=a4i.toRingHom)).of_dvd
    apply minpoly.dvd
    rw [aeval_def,zem]
    change (minpoly tJ x).eval₂
      ((z12 SF HR).comp (z12 tJ SF)) (l x)=0
    rw [← zYY tJ SF HR,← aeval_def,
      aeval_algHom_apply l,minpoly.aeval,zhc]
  refine ⟨a 0,a 1,?_,hsep' _ (hsep 0),hsep' _ (hsep 1)⟩
  have hc: (zdq (Qr.PW (a 0) (a 1))).comap iJ =
      (zdq (Qr.aaU y v)).comap iJ:= by
    rw [ddb hyv,zEW,hchart,zGm _ l.injective,
      hker]
  ext Q
  obtain ⟨P,rfl⟩:=gBQ Q
  exact Iff.of_eq (zPw (fun I:znc Jet=>P∈I) hc)
end
end baD
end
section
namespace aZb
noncomputable section
open K1 cu gT Qr
private theorem aWl (i j:Fin 4) :Function.Commute (ER i) (ER j) := by
 intro Q
 by_cases hij:i=j
 · subst j
   rfl
 apply MvPolynomial.ext
 intro d
 simp only [ER,zcl,Finsupp.add_apply,Finsupp.single_apply,
   zNB hij,zNB (Ne.symm hij),z0a]
 rw [add_right_comm d (zhf i 1) (zhf j 1)]
 ring
private def kK (P:Jet) (a b c d:ℕ) :Ambient :=
 (ER 2)^[c] ((ER 3)^[d] ((ER 0)^[a] ((ER 1)^[b] (iJ P))))
private theorem eA0 (P:Jet) (a b c d:ℕ) :
  ER 0 (kK P a b c d)=kK P (a+1) b c d:= by
 unfold kK
 rw [((aWl 0 2).iterate_right c).eq,((aWl 0 3).iterate_right d).eq,
  zLk]
private theorem eA1 (P:Jet) (a b c d:ℕ) :
  ER 1 (kK P a b c d)=kK P a (b+1) c d:= by
 unfold kK
 rw [((aWl 1 2).iterate_right c).eq,((aWl 1 3).iterate_right d).eq,
  ((aWl 1 0).iterate_right a).eq,zLk]
private theorem eAU (P:Jet) (a b c d:ℕ) :
  ER 3 (kK P a b c d)=kK P a b c (d+1) := by
 unfold kK
 rw [((aWl 3 2).iterate_right c).eq,zLk]
private theorem eAM (P:Jet) (a b:ℕ) :
  kK P a b 0 0=b.factorial•a.factorial•iJ (A5 0 a (A5 1 b P)) := by
 have hcomm:Function.Commute (fun Q:z87=>b.factorial•Q) (ER 0) :=
  fun Q=>(map_nsmul (zWe (R:=FX) (0:Fin 4)) b.factorial Q).symm
 have h0 (Q:Jet) :
   (ER 0)^[a] (iJ Q)=a.factorial•iJ (A5 0 a Q) :=bNJ 0 a Q
 have h1 :
   (ER 1)^[b] (iJ P)=b.factorial•iJ (A5 1 b P) :=bNJ 1 b P
 simp only [kK,z56,h1,← (hcomm.iterate_right a).eq,h0]
private theorem eAN {I:znc z87} (hI:bAH I)
    {P:Jet} {m:ℕ} (hP:bQ5 I P m) :
    ∀ a b c d,a+b+c+d< m→kK P a b c d∈I:= by
  suffices ∀ k a b c d,c+d=k→a+b+c+d< m→kK P a b c d∈I by
    exact fun a b c d h=>this (c+d) a b c d rfl h
  intro k
  induction k using z0n with
  | h k ih =>
    have step (a b c d:ℕ) (hk :c+d<k) (ht:a+b+c+d+1< m) :
        ER 2 (kK P a b c d)∈I∧ER 3 (kK P a b c d)∈I:= by
      apply gAn hI (ih (c+d) hk a b c d rfl (by omega))
      · change ER 0 (kK P a b c d)∈I
        rw [eA0]
        exact ih (c+d) hk (a+1) b c d rfl (by omega)
      · change ER 1 (kK P a b c d)∈I
        rw [eA1]
        exact ih (c+d) hk a (b+1) c d rfl (by omega)
    intro a b c d hk ht
    cases c with
    | succ c =>
      have h:=(step a b c d (by omega) (by omega)).1
      simpa only [kK,zLk] using h
    | zero =>
      cases d with
      | zero =>
        rw [eAM]
        exact nsmul_mem (nsmul_mem (hP a b (by omega)) _) _
      | succ d =>
        exact (eAU P a b 0 d) ▸ (step a b 0 d (by omega) (by omega)).2
theorem proof :Qr.c2 := by
 intro I hI P m hm hP y v hy a b hab
 have h:=eAN hI hP 0 0 a b (by omega)
 have hev :aaU y v ((ER 2)^[a] ((ER 3)^[b] (iJ P)))=0:= by
  apply RingHom.mem_ker.mp
  rw [show zdq (aaU y v)=I from hy]
  simpa only [kK,z56] using h
 rw [d2x] at hev
 simp only [zVT] at hev
 let:CharP zH p:=zgG (z12 K zH).injective p
 have hp:=CharP.char_is_prime_of_two_le K p (by decide)
 have hfac (n:ℕ) (hn:n<p) : (n.factorial:zH)≠0:= by
  intro hz
  exact (ziF hn) (hp.dvd_factorial.mp ((zX2 zH p _).mp hz))
 exact (mul_eq_zero.mp ((mul_eq_zero.mp hev).resolve_left (hfac a (by omega)))).resolve_left
  (hfac b (by omega))
end
end aZb
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace aBb
noncomputable section
open cu gT Polynomial
open scoped BigOperators
private abbrev a5j:aZ →+* z3y (Fin 2) aQ :=
 zDK (z12 FX aQ)
private def Yn:aQ[X] :=
 z1z (ek 1)-Polynomial.C (ek 0)*z7y
private def substitute :z3y (Fin 2) aQ →ₐ[aQ] aQ[X] :=
 zIe ![Yn,z7y]
private def aJw (P:aZ) :aQ[X] :=substitute (a5j P)
private theorem gsG :
   zq4 (zqf (z12 FX aQ) (-ek 0)) := by
 let f :FX[X] →+* aZ:=zqf znf (-MvPolynomial.X 0)
 let g:aZ →+* FX[X] :=
   zOD z1z ![-Polynomial.X,0]
 have hfg:g.comp f=zz5 _:= by
   apply z86
   · intro r
     simp [f,g,z4Q]
   · simp [f,g,z4Q]
 have hf :Function.LeftInverse g f := fun x=>zLs hfg x
 have he : (z12 aZ aQ).comp f =
     zqf (z12 FX aQ) (-ek 0) := by
   apply z86
   · intro r
     simp only [zQb,f,z4Q,zJU]
     rw [zG3 FX aZ aQ]
     rfl
   · simp [f,z4Q,ek]
 rw [← he]
 exact (zxb aZ aQ).comp hf.injective
private theorem aXY (m:Fin 2 →₀ ℕ) :m.sum (fun _ n=>n)=m 0+m 1 := by
 simp [Finsupp.sum_of_support_subset m (Finset.subset_univ m.support)]
private theorem gsi (P:aZ) (hP:P≠0) :
    (aJw P).natDegree=P.totalDegree := by
  classical
  let d:=P.totalDegree
  let term (m:Fin 2 →₀ ℕ) :=
    z1z (z12 FX aQ (P.coeff m))*Yn^m 0*z7y ^m 1
  have hsum:aJw P = ∑ m∈P.support,term m:= by
    conv_lhs=>rw [aJw,P.as_sum,zdo,zdo]
    apply zUo rfl
    intro m hm
    rw [MvPolynomial.map_monomial]
    simp only [substitute,MvPolynomial.aeval_def,MvPolynomial.eval₂_monomial,
      term,zrE]
    rw [z6B _ _ (fun i=>zJx _),Fin.prod_univ_two]
    simp [ztg]
  have hi:Yn.natDegree≤1 := by
    unfold Yn
    have hm: (z1z (ek 0)*z7y).natDegree≤1 :=
      (zRn _ _).trans (by simp)
    simpa using Polynomial.natDegree_sub_le_of_le (p:=z1z (ek 1))
      (show (z1z (ek 1)).natDegree≤1 from by simp) hm
  have hi₁:Yn.coeff 1 = -ek 0:= by
    simp [Yn]
  have hterm (m:Fin 2 →₀ ℕ) : (term m).natDegree≤ m 0+m 1 := by
    apply zJZ
    · exact (zRn _ _).trans
        (by simpa using zxc (m 0) hi)
    · simp
  have hle (m:Fin 2 →₀ ℕ) (hm:m∈P.support) :m 0+m 1≤d:= by
    simpa only [aXY] using MvPolynomial.le_totalDegree hm
  refine zWs ?_ (zZI ?_)
  · rw [hsum]
    exact zMZ _ _ (fun m hm=>(hterm m).trans (hle m hm))
  let top:=P.support.filter (fun m=>m 0+m 1=d)
  let slopePoly :FX[X] := ∑ m∈top,z1z (P.coeff m)*z7y ^m 0
  have hcoeff :
      (aJw P).coeff d=zqf (z12 FX aQ) (-ek 0) slopePoly := by
    dsimp only [slopePoly,top]
    rw [hsum,zaW,zdo,Finset.sum_filter]
    apply zUo rfl
    intro m hm
    by_cases he :m 0+m 1=d
    · rw [zYo he,← he]
      dsimp only [term]
      rw [Polynomial.coeff_mul_X_pow,Polynomial.coeff_C_mul]
      have hp:=Polynomial.coeff_pow_of_natDegree_le (m:=m 0) hi
      rw [zqe] at hp
      rw [hp,hi₁]
      simp [z4Q]
    · rw [zNB he,zQl
        ((hterm m).trans_lt (lt_of_le_of_ne (hle m hm) he))]
  obtain ⟨e,he,hed⟩:=Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hP) (fun m=>m.sum (fun _ n=>n))
  have ht:e∈top:=Finset.mem_filter.mpr ⟨he,by
    change e 0+e 1=P.support.sup (fun m=>m.sum (fun _ n=>n))
    rw [← aXY,hed]⟩
  have hslope :slopePoly≠0:= by
    have hc:slopePoly.coeff (e 0)=P.coeff e := by
      dsimp only [slopePoly]
      rw [zaW,zpa e ht]
      · simp
      · intro m hm hme
        have hi0:e 0≠m 0:= by
          intro he0
          have he1 :e 1=m 1 := by
            have h₁:=(Finset.mem_filter.mp ht).2
            have h₂:=(Finset.mem_filter.mp hm).2
            omega
          apply hme
          ext i
          fin_cases i
          · exact he0.symm
          · exact he1.symm
        simp [hi0]
    exact fun hz=>MvPolynomial.mem_support_iff.mp he (by rw [← hc,hz,zO6])
  rw [hcoeff]
  exact fun hz=>hslope (gsG (hz.trans (zhc _).symm))
private def eLC (P:aZ) :
    aLP (zye {P}) ≃ₐ[aQ] (aQ[X] ⧸ zye {aJw P}) := by
  let J:znc (z3y (Fin 2) aQ) :=
    (zye {P}).map a5j ⊔ zye {B4 0 1}
  let A:=z3y (Fin 2) aQ ⧸ J
  let B:=aQ[X] ⧸ zye {aJw P}
  let j:=zvR aQ J
  let k :=zvR aQ (zye {aJw P})
  have h0:substitute (z9v 0)=Yn:= by simp [substitute]
  have h1 :substitute (z9v 1)=Polynomial.X:= by simp [substitute]
  have hline :substitute (B4 0 1)=0:= by
    simp only [B4,zpO,zrl,zok,zWj,
      h0,h1,zrE,Yn,sub_add_cancel,sub_self]
  have hmap :J=zye {a5j P} ⊔ zye {B4 0 1} := by
    change (zye {P}).map a5j ⊔ _ = _
    rw [Ideal.map_span,zyk]
  have hjP:j (a5j P)=0:= by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hmap]
    exact zKg (zCn (zT1 _))
  have hjLine :j (B4 0 1)=0:= by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (zs0 (zCn (zT1 _)))
  let f :A →ₐ[aQ] B:=zTA J (k.comp substitute) (by
    intro x hx
    have h:J≤zdq (k.comp substitute).toRingHom:= by
      rw [hmap]
      refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · rintro x (rfl :x=a5j P)
        exact RingHom.mem_ker.mpr (Ideal.Quotient.mk_singleton_self _)
      · rintro x (rfl :x=B4 0 1)
        apply RingHom.mem_ker.mpr
        change k (substitute _)=0
        rw [hline,zhc]
    exact h hx)
  let p:aQ[X] →ₐ[aQ] A:=zEU (j (z9v 1))
  have hp:p.comp substitute=j:= by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change p (substitute (z9v 0))=j (z9v 0)
      rw [h0]
      simp only [p,Yn,zpO,zok,Polynomial.aeval_C,zw0]
      simp only [B4,zpO,zrl,zok,zWj] at hjLine
      rw [sub_eq_zero] at hjLine
      exact sub_eq_of_eq_add hjLine.symm
    · change p (substitute (z9v 1))=j (z9v 1)
      rw [h1]
      exact zw0 _
  let g:B →ₐ[aQ] A:=zTA _ p (by
    intro x hx
    have h:zye {aJw P} ≤ zdq p.toRingHom:= by
      apply Ideal.span_le.mpr
      rintro x (rfl :x=aJw P)
      exact RingHom.mem_ker.mpr ((zmU hp (a5j P)).trans hjP)
    exact h hx)
  apply AlgEquiv.ofAlgHom f g
  · apply AlgHom.ext
    intro x
    obtain ⟨x,rfl⟩:=zld x
    have h: (f.comp g).comp k=k := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply]
      have hg:g (k z7y)=j (z9v 1) := by
        change p z7y=j (z9v 1)
        exact zw0 _
      rw [hg]
      change k (substitute (z9v 1))= _
      rw [h1]
    exact zmU h x
  · apply AlgHom.ext
    intro x
    obtain ⟨x,rfl⟩:=zld x
    exact zmU hp x
theorem eLN (P:aZ) (hP:P≠0) :
  zsE aQ (aLP (zye {P}))=P.totalDegree := by
 calc
  _=zsE aQ (aQ[X] ⧸ zye {aJw P}) :=
    (eLC P).toLinearEquiv.finrank_eq
  _ = _:=finrank_quotient_span_eq_natDegree.trans (gsi P hP)
end
end aBb
end
section
namespace BN
noncomputable section
open K1 Polynomial
def afT {u T R D} (B:KJ u T R D) (l:Fin 2) :K[X] :=
 B.a*(B.β l).map twist
def c4b (d:ℕ) (u:e9) (deleted:zJe I) (U V:Fin 2→K[X])
    (O:Fin 2→Fin 2→K[X]) :Prop :=
  ∀ i∉deleted,∀ j l,(U l).eval (node i)*u j i+(V j).eval (node i)*(u l i)^d =
    (O j l).eval (node i)
structure lK (u:e9) (deleted:zJe I) (h:ℕ) (U V:Fin 2→K[X]) where
 output :Fin 2→Fin 2→K[X]
 U_ne : ∃ l,U l≠0
 V_ne : ∃ j,V j≠0
 height_eq :max (uO (U 0) (U 1)) (uO (V 0) (V 1))=h
 primitive : ∀ f :K[X],(∀ l,f∣U l)→(∀ j,f∣V j)→ zWB f
 output_degree : ∀ j l,(output j l).degree<(131072+h:ℕ)
 nodes :c4b p u deleted U V output
structure Adjugate (u:e9) (deleted:zJe I) (h:ℕ) where
 denom:K[X]
 nonzero :denom≠0
 denom_degree :denom.natDegree≤2*h
 Fr :Fin 2→K[X]
 numer_degree : ∀ j,(Fr j).degree<(131072+2*h:ℕ)
 nodes : ∀ i∉deleted,∀ j,denom.eval (node i)*u j i=(Fr j).eval (node i)
abbrev qC:=z3y (Fin 2) K
structure adh where
 poly :z3y (Fin 2) qC
 nonzero :poly≠0
 y_degree :poly.degreeOf 1≤5
 s_degree : ∀ e∈poly.support,(poly.coeff e).degreeOf 0≤26
 t_degree : ∀ e∈poly.support,(poly.coeff e).degreeOf 1≤21
 total : ∀ e∈poly.support,e 1+(poly.coeff e).totalDegree≤37
def adh.auh (A:adh) (γ:K) :z3y (Fin 2) K :=
 A.poly.map (zY9 ![γ,γ^p])
def adh.aSV (A:adh) (γ:K) (P:K[X]) :K[X] :=
 zIe ![z7y,P] (A.auh γ)
def acN (d b s t:ℕ) :ℕ :=
  ∑ i∈z4x (b+1),∑ j∈z4x (b+1 - i),
    (d+1 - 131071*(i+j))*(s+1-i)*(t+1-j)
def adQ (m s t:ℕ) :ℕ :=
 ∑ i∈z4x m,∑ j∈z4x (m-i),(m-i-j)*(s+1-i)*(t+1-j)
end
end BN
end
section
namespace aez
noncomputable section
open K1 wT MvPolynomial
def GA (h:ℕ) :Fin 4→ℕ := ![131071+h,1,1,1]
def Om:zM1 K →+* z3y (Fin 4) K :=
 zqf znf (z9v 0)
def qW (A:Fin 2→zM1 K) (z :z3y (Fin 4) K) :
    z3y (Fin 4) K :=
  Om (A 0)+z*Om (A 1)
def denominator (V:Fin 2→zM1 K) :z3y (Fin 4) K :=
 qW V (z9v 2)
def numerator (U:Fin 2→zM1 K) (O:Fin 2→Fin 2→zM1 K) :
    z3y (Fin 4) K :=
  qW (fun j=>O j 0) (z9v 2)+MvPolynomial.X 3*qW (fun j=>O j 1) (z9v 2) -
    qW U (z9v 3)*z9v 1
def aEc (U V:Fin 2→zM1 K) (O:Fin 2→Fin 2→zM1 K) :
    z3y (Fin 5) K :=
  xx.symm (z1z (denominator V)*z7y-Polynomial.C (numerator U O))
theorem bgd (U V:Fin 2→zM1 K) (O:Fin 2→Fin 2→zM1 K) :
  xx (aEc U V O) =
   z1z (denominator V)*z7y-Polynomial.C (numerator U O) :=
 xx.apply_symm_apply _
def ddP (u:e9) (i:I) :z3y (Fin 5) K →ₐ[K] z3y (Fin 5) K :=
 Ko (node i) (u 0 i) (u 1 i) (u 0 i^p) (u 1 i^p)
end
end aez
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace aez
noncomputable section
open MvPolynomial wT
variable {F:Type*} [zrb F] {N :ℕ} {L:z3y (Fin 5) F}
structure awZ (N :ℕ) (L:z3y (Fin 5) F) where
 x :Fin N→F
 first:Fin N→F
 firstSlope :Fin N→F
 second:Fin N→F
 secondSlope :Fin N→F
 order_one : ∀ i,(RK oH
   (Ko (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree=1
def awZ.ic (C:awZ N L) (i:Fin N) :=
 Ko (C.x i) (C.first i) (C.firstSlope i) (C.second i) (C.secondSlope i)
variable (C:awZ N L) {h:ℕ}
 (hdeg : ∀ j,L.weightedTotalDegree (vO 131071 j)=GA h j)
end
end aez
end
section
namespace agK
noncomputable section
open K1 MvPolynomial
open scoped Polynomial
abbrev af :=z3y (Fin 3) K[X]
abbrev ko:=z3y (Fin 3) kB
def jW (γ:K) (P:K[X]) :Fin 3→K[X] :=
 ![P,z1z γ,z1z (γ^p)]
def OT (g:af) (γ:K) (P:K[X]) :K[X] :=
 zY9 (jW γ P) g
def ayE (g:af) (j:Fin 5) :af :=
 (zWe (R:=K[X]) (0:Fin 3))^[j.val] g
def ae8 (g:af) (γ:K) (P:K[X]) :Prop :=
 OT g γ P=0∧OT (zWe 0 g) γ P≠0
def bC (g:af) :ko :=
 zDK (z12 K[X] kB) g
def point (γ:K) (P:K[X]) :Fin 3→kB :=
 (z12 K[X] kB) ∘ jW γ P
end
end agK
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace agK
noncomputable section
open MvPolynomial
open scoped BigOperators
private theorem a5X {A:Type*} (S:zJe A) (aa0:Set A) [DecidablePred (· ∈ aa0)] :
  ((S:Set A)∩aa0).ncard=(S.filter (· ∈ aa0)).card:= by
 rw [← zik,Finset.coe_filter]
 rfl
private theorem caj {F σ:Type*} [zrb F] [Finite σ]
    (J:znc (z3y σ F)) [J.IsPrime] (x :σ→F) (hx :x∈zSD F J) :
    1≤zHf J:= by
  classical
  generalize hd: (zIU J).natDegree=d
  induction d using z0n generalizing J with
  | h d ih =>
    by_cases h0:d=0
    · have hfin:=z1b (K:=F) J (hd.trans h0)
      have hxone :1≤(zSD F J).ncard:= by
        simpa using zDB (Set.singleton_subset_iff.mpr hx) hfin.1
      exact (by exact_mod_cast hxone : (1 :ℚ)≤_).trans hfin.2
    have hproper : ∃ i,z9v i - C (x i)∉J:= by
      by_contra hn
      push Not at hn
      let φ:=zVv J
      have hmaps :φ=φ.comp (C.comp (zY9 x)) := by
        apply zXT
        · intro c
          simp [φ]
        · intro i
          simp only [zQb,zV6]
          exact sub_eq_zero.mp (by rw [← zpO]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hn i))
      have hsurj:zpX (z12 F (z3y σ F ⧸ J)) := by
        intro q
        obtain ⟨g,rfl⟩:=zld q
        refine ⟨zY9 x g,?_⟩
        exact (zLs hmaps g).symm
      have :zAa F (z3y σ F ⧸ J) :=
        Module.Finite.of_surjective (Algebra.linearMap F (z3y σ F ⧸ J)) hsurj
      exact h0 (by rw [← hd,affineHilbertPolynomial_eq_C_finrank,Polynomial.natDegree_C])
    obtain ⟨i,hi⟩:=hproper
    let f :=z9v i - C (x i)
    have hxf :zIe x f=0:= by simp [f]
    have hfdeg:f.totalDegree≤1 := by
      exact (totalDegree_sub _ _).trans (by simp)
    have hxp:x∈zSD F (J ⊔ zye {f}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx,hxf⟩
    obtain ⟨Q,hQ,hxQ⟩:=zwb
      (J ⊔ zye {f}) (1 :z3y σ F) x hxp (by simp)
    have hQmin:=(Ideal.mem_retainedMinimalPrimes.mp hQ).1
    have :Q.IsPrime :=hQmin.isPrime
    have hd' := zdH hi hQmin
    have hone :=ih _ (by omega) Q hxQ rfl
    have hsum:=zcE
      (1 :z3y σ F) hi hfdeg
    have hQsum:=zfK (f :=zHf)
      (fun A _=>zcN A) hQ
    simpa only [Nat.cast_one,one_mul] using hone.trans (hQsum.trans hsum)
private theorem ccD {F σ ι:Type*} [zrb F] [Finite σ] [Fintype ι]
    (s :z3y σ F) (cuts :ι→z3y σ F) {A L M:ℕ}
    (hLA:L≤A) (hdeg : ∀ i,(cuts i).totalDegree≤M) {R:ℚ} (hR:1≤R)
    (hratio : ∀ m<L,(((zhP ι - m)*M:ℕ) :ℚ)≤R*((A - m:ℕ) :ℚ))
    (S:zJe (σ→F)) (hreg : ∀ x∈S,zIe x s≠0)
    (hA : ∀ x∈S,A ≤ {i | zIe x (cuts i)=0}.ncard)
    (hterminal : ∀ J:znc (z3y σ F),L ≤ {i | cuts i∈J}.ncard →
      (((S:Set (σ→F))∩zSD F J).ncard:ℚ)≤R)
    (P:znc (z3y σ F)) [P.IsPrime] (W:zJe (σ→F)) (hW:W⊆S)
    (hzero : ∀ x∈W,x∈zSD F P) :
    (W.card:ℚ)≤zHf P*R^(zIU P).natDegree := by
  classical
  generalize hd: (zIU P).natDegree=d
  induction d using z0n generalizing P W with
  | h d ih =>
    rcases W.eq_empty_or_nonempty with rfl | ⟨x₀,hx₀⟩
    · simpa using mul_nonneg (zcN P) (pow_nonneg (zero_le_one.trans hR) d)
    rcases d with _ | e
    · have hfin:=z1b (K:=F) P hd
      have hcard:=zDB
        (fun x (hx :x∈(W:Set (σ→F)))=>hzero x hx) hfin.1
      rw [zik] at hcard
      simpa using (by exact_mod_cast hcard: (W.card:ℚ)≤_).trans hfin.2
    let keep:zJe ι:=Finset.univ.filter fun i=>cuts i∈P
    have hkeep:keep.card = {i | cuts i∈P}.ncard:= by
      rw [← zik]
      congr 1
      ext i
      simp [keep]
    by_cases hpers :L≤keep.card
    · have hc:W.card≤((S:Set (σ→F))∩zSD F P).ncard:= by
        rw [← zik]
        exact zDB (fun x hx=>⟨hW hx,hzero x hx⟩)
      have hdegP:=caj P x₀ (hzero x₀ hx₀)
      calc
        (W.card:ℚ)≤(((S:Set (σ→F))∩zSD F P).ncard:ℚ) := by exact_mod_cast hc
        _≤R:=hterminal P (hkeep ▸ hpers)
        _≤zHf P*R^(e+1) := by
          calc
            R=1*R^(1 :ℕ) := by ring
            _≤zHf P*R^(e+1) :=
              mul_le_mul hdegP (pow_le_pow_right₀ hR (by omega)) (by positivity) (by linarith)
    let rel : (σ→F)→ι→Prop := fun x i=>zIe x (cuts i)=0
    let c:ℚ:=((A - keep.card:ℕ) :ℚ)
    have hc:0<c:= by
      change (0:ℚ)<((A - keep.card:ℕ) :ℚ)
      exact_mod_cast (by omega :0<A - keep.card)
    have hlowNat :W.card*(A - keep.card) ≤ ∑ i∈keepᶜ,(W.bipartiteBelow rel i).card:= by
      refine Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow rel keep fun x hx => ?_
      rw [← zik,Finset.coe_bipartiteAbove]
      simpa [rel] using hA x (hW hx)
    have hlow: (W.card:ℚ)*c ≤ ∑ i∈keepᶜ,((W.bipartiteBelow rel i).card:ℚ) := by
      change (W.card:ℚ)*((A - keep.card:ℕ) :ℚ)≤_
      exact_mod_cast hlowNat
    have hcut : ∀ i∈keepᶜ,((W.bipartiteBelow rel i).card:ℚ)≤M*zHf P*R^e := by
      intro i hi
      have hiP:cuts i∉P:= by simpa [keep] using hi
      rw [← zik,Finset.coe_bipartiteBelow]
      refine ncard_inter_cut_le_of_retained_le s hiP (hdeg i) W
        (fun x hx=>⟨hzero x hx,hreg x (hW hx)⟩) (by positivity) fun Q hQ => ?_
      have hQmin:=(Ideal.mem_retainedMinimalPrimes.mp hQ).1
      have :Q.IsPrime :=hQmin.isPrime
      have hQdim: (zIU Q).natDegree=e := by
        have :=zdH hiP hQmin
        omega
      rw [a5X]
      exact ih e (by omega) Q _ (fun _ hx=>hW (Finset.mem_filter.mp hx).1)
        (fun _ hx=>(Finset.mem_filter.mp hx).2) hQdim
    have hupp : ∑ i∈keepᶜ,((W.bipartiteBelow rel i).card:ℚ) ≤
        ((zhP ι - keep.card:ℕ) :ℚ)*(M*zHf P*R^e) := by
      refine (Finset.sum_le_card_nsmul _ _ _ hcut).trans_eq ?_
      rw [zVT,Finset.card_compl]
    refine le_of_mul_le_mul_right (hlow.trans (hupp.trans ?_)) hc
    calc
      ((zhP ι - keep.card:ℕ) :ℚ)*(M*zHf P*R^e) =
          (((zhP ι - keep.card)*M:ℕ) :ℚ)*(zHf P*R^e) := by
        rw [z2R]
        ring
      _≤(R*c)*(zHf P*R^e) :=
        mul_le_mul_of_nonneg_right (hratio keep.card (by omega))
          (mul_nonneg (zcN P) (pow_nonneg (zero_le_one.trans hR) e))
      _=(zHf P*R^(e+1))*c:= by rw [pow_succ]; ring
theorem bxi {F ι:Type*} [zrb F] [Fintype ι]
   (g s :z3y (Fin 3) F) (hg:g≠0) (cuts :ι→z3y (Fin 3) F)
   {A L M E :ℕ} (hLA:L≤A) (hgdeg:g.totalDegree≤E) (hdeg : ∀ i,(cuts i).totalDegree≤M)
   {R:ℚ} (hR:1≤R)
   (hratio : ∀ m<L,(((zhP ι - m)*M:ℕ) :ℚ)≤R*((A - m:ℕ) :ℚ))
   (S:zJe (Fin 3→F)) (hS : ∀ x∈S,zIe x g=0∧zIe x s≠0)
   (hA : ∀ x∈S,A ≤ {i | zIe x (cuts i)=0}.ncard)
   (hterminal : ∀ J:znc (z3y (Fin 3) F),L ≤ {i | cuts i∈J}.ncard →
     (((S:Set (Fin 3→F))∩zSD F J).ncard:ℚ)≤R) :
   (S.card:ℚ)≤E*R^2 := by
 classical
 let family :=(zye {g}).retainedMinimalPrimes s
 have hmem (Q) (hQ:Q∈family) :g∈Q :=
   (Ideal.mem_retainedMinimalPrimes.mp hQ).1.le (z5J g)
 have hdim : ∀ Q∈family,(zIU Q).natDegree≤2 := by
   intro Q hQ
   simpa [Nat.card_eq_fintype_card] using natDegree_affineHilbertPolynomial_le_of_mem hg (hmem Q hQ)
 have hsum : ∑ Q∈family,zHf Q≤(E :ℚ) := by
   have : (⊥ : znc (z3y (Fin 3) F)).IsPrime :=Ideal.isPrime_bot
   have hnot:g∉(⊥ : znc (z3y (Fin 3) F)) := by simpa using hg
   simpa only [family,bot_sup_eq,affineDegree_bot,zqe] using
     zcE s hnot hgdeg
 refine card_le_mul_pow_of_forall_mem_zeroLocus family hdim hsum hR S (fun x hx => ?_) ?_
 · have hxg:x∈zSD F (zye {g}) :=mem_zeroLocus_iff_le_ker_aeval.mpr
     ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hS x hx).1))
   exact zwb _ s x hxg (hS x hx).2
 · intro Q hQ
   have :Q.IsPrime :=(Ideal.mem_retainedMinimalPrimes.mp hQ).1.isPrime
   rw [a5X]
   exact ccD s cuts hLA hdeg hR hratio S
     (fun x hx=>(hS x hx).2) hA hterminal Q _
     (fun _ hx=>(Finset.mem_filter.mp hx).1) (fun _ hx=>(Finset.mem_filter.mp hx).2)
end
end agK
end
section
namespace bzp
noncomputable section
open K1 agK MvPolynomial
open scoped Polynomial BigOperators
def dx (f :af) :af :=
 ∑ m∈f.support,monomial m (f.coeff m).derivative
abbrev dy (f :af) :af :=zWe 0 f
def Bd (g f :af) :af :=
 dy g*dx f - dx g*dy f
def numerator (g:af) :ℕ→af
  | 0 => -dx g
  | n+1=>dy g*Bd g (numerator g n) -
    znf ((2*n+1 :ℕ) :K[X])*Bd g (dy g)*numerator g n
@[simp] private theorem bXI (f :af) (m:Fin 3 →₀ ℕ) :
    (dx f).coeff m=(f.coeff m).derivative := by
  classical
  rw [dx,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,zhc]
private theorem dYG (c:K[X]) :
  dx (znf c)=znf c.derivative := by
 classical
 apply MvPolynomial.ext
 intro m
 rw [bXI]
 by_cases hm:0=m <;> simp [MvPolynomial.coeff_C,hm]
private theorem dYH (f q:af) :dx (f+q)=dx f+dx q:= by
 ext m
 simp
private theorem dYJ (f :af) (j:Fin 3) :
  dx (f*z9v j)=dx f*z9v j:= by
 classical
 ext m
 rw [bXI,z0S,z0S]
 split_ifs <;> simp
private theorem ctV (γ:K) (P:K[X]) (f :af) :
    (OT f γ P).derivative=OT (dx f) γ P +
      P.derivative*OT (dy f) γ P:= by
  have hconstant (j:Fin 3) (hj:j≠0) : (jW γ P j).derivative=0:= by
    fin_cases j
    · exact (hj rfl).elim
    · exact zJH
    · exact zJH
  unfold OT
  induction f using z5i with
  | C c=>simp [dYG]
  | add f q hf hq =>
    simp only [zrl,dYH,hf,hq,dy,mul_add]
    ring
  | mul_X f j ih =>
    rw [zok,zV6,zAg,ih,dYJ,
      zok,zV6]
    simp only [dy,zGW,zrl,zok,zV6]
    by_cases hj:j=0
    · subst j
      rw [show (jW γ P 0).derivative=P.derivative from rfl,
        MvPolynomial.pderiv_X_self,map_one]
      ring
    · rw [hconstant j hj,zVY hj,zhc]
      ring
private theorem bpy (g f :af) (γ:K) (P:K[X]) (hg:OT g γ P=0) :
  OT (Bd g f) γ P=OT (dy g) γ P*(OT f γ P).derivative := by
 have hz :OT (dx g) γ P+P.derivative*OT (dy g) γ P=0:= by
  rw [← ctV,hg,zhc]
 rw [ctV]
 simp only [Bd,OT,zpO,zok]
 unfold OT at hz
 linear_combination -MvPolynomial.eval (jW γ P) (dy f)*hz
private theorem anS (a :ℕ) (U V:K[X]) :
   U*(U*(U^a*V).derivative)-(a :K[X])*(U*U.derivative)*(U^a*V) =
     U^(a+2)*V.derivative := by
 cases a with
 | zero=>simp [pow_two,mul_assoc]
 | succ a =>
   rw [zAg,Polynomial.derivative_pow,Nat.succ_sub_one,
     pow_add U (a+1) 2,pow_succ' U a]
   simp only [Polynomial.C_eq_natCast]
   push_cast
   ring
theorem b12 (g:af) (γ:K) (P:K[X])
    (hg:OT g γ P=0) (n:ℕ) :
    OT (numerator g n) γ P =
      OT (dy g) γ P^(2*n+1)*((zst (R:=K))^[n+1]) P:= by
  induction n with
  | zero =>
    have hz :=ctV γ P g
    rw [hg,zhc] at hz
    change zY9 (jW γ P) (-dx g)= _
    rw [map_neg]
    change -OT (dx g) γ P= _
    simp only [zbc,zvM,pow_one,Function.iterate_one]
    linear_combination hz
  | succ n ih =>
    change zY9 (jW γ P) (_-_)= _
    rw [zpO,zok,zok,zok,z9X]
    change OT (dy g) γ P*OT (Bd g (numerator g n)) γ P -
      ((2*n+1 :ℕ) :K[X])*OT (Bd g (dy g)) γ P *
        OT (numerator g n) γ P= _
    rw [bpy _ _ _ _ hg,bpy _ _ _ _ hg,ih,anS,
      show 2*(n+1)+1=2*n+1+2 by omega]
    congr 1
    exact (zLk _ _ _).symm
private theorem bEp (f :af) : (dx f).totalDegree≤f.totalDegree := by
 classical
 apply totalDegree_le_of_support_subset
 intro m hm
 contrapose! hm
 rw [MvPolynomial.notMem_support_iff] at hm ⊢
 rw [bXI,hm,zhc]
private theorem b1h (f :af) : (dy f).totalDegree≤f.totalDegree - 1 := by
 simpa only [weightedTotalDegree_one,Pi.one_apply] using
  weightedTotalDegree_pderiv_le_sub (1 :Fin 3→ℕ) (0:Fin 3) f
end
end bzp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace agK
noncomputable section
open K1 BN MvPolynomial
open scoped Polynomial
private theorem eKQ (g:af) :
  (zWe (0:Fin 3) g).totalDegree≤g.totalDegree := by
 simpa only [weightedTotalDegree_one] using
  weightedTotalDegree_pderiv_le (1 :Fin 3→ℕ) (0:Fin 3) g
private theorem bD8 (g:af) (j:Fin 5) :
    (ayE g j).totalDegree≤g.totalDegree := by
  have h (n:ℕ) :
      (((zWe (R:=K[X]) (0:Fin 3))^[n]) g).totalDegree ≤
        g.totalDegree := by
    induction n with
    | zero=>exact le_rfl
    | succ n ih =>
      rw [zLk]
      exact (eKQ _).trans ih
  exact h j.val
private theorem aC5 (g:af) (γ:K) (P:K[X]) :
  zY9 (point γ P) (bC g)=z12 K[X] kB (OT g γ P) := by
 rw [bC,znM]
 exact (z6r (z12 K[X] kB) (jW γ P) g).symm
end
end agK
end
section
namespace bzp
noncomputable section
open K1 agK MvPolynomial
open scoped Polynomial BigOperators
private def width :ℕ:=131071
private def ahp:ℕ:=2*width - 1
private abbrev afH :K[X] →+* kB:=z12 K[X] kB
private abbrev embed:K →+* kB:=afH.comp z1z
private abbrev centre :kB:=afH z7y
private theorem cMM (P:K[X]) : (P.map embed).eval centre=afH P:= by
 rw [zhI]
 simpa only [z8i] using
  (zly P z1z afH z7y).symm
private theorem d53 {n:ℕ} (hn:n<p) : (n.factorial:kB)≠0:= by
 let:CharP kB p:=zgG embed.injective p
 induction n with
 | zero=>simp
 | succ n ih =>
   have hc: ((n+1 :ℕ) :kB)≠0:= by
     intro hz
     have hd:=(zX2 kB p (n+1)).mp hz
     exact (ziF hn) (zTm (ztH n) hd)
   simpa only [zwO,z2R] using
     mul_ne_zero hc (ih (zws hn))
private abbrev ZC (P:K[X]) (n:ℕ) :kB :=
 afH (((zst (R:=K))^[n]) P)
private def asv (x :K) (n:ℕ) :kB :=
 (n.factorial:kB)⁻¹*(embed x - centre)^n
private theorem gAQ (P:K[X]) (x :K) (n:ℕ) (hn:n<p) :
    (zcJ centre (P.map embed)).coeff n*(embed x - centre)^n =
      ZC P n*asv x n:= by
  rw [zWQ,zvb,cMM]
  have h:=congrFun (z6T (R:=K) n) P
  have hfactor :ZC P n=(n.factorial:kB)*afH (z75 n P) := by
    unfold ZC
    rw [← h]
    simp only [zqa]
    rw [zVT,zok,zGu]
  rw [hfactor,asv]
  symm
  calc
    _=(afH (z75 n P)*(embed x - centre)^n) *
        ((n.factorial:kB)*(n.factorial:kB)⁻¹) := by ring
    _ = _:= by rw [mul_inv_cancel₀ (d53 hn),zqe]
private theorem bds (P:K[X]) (hP:P.degree<131072) (x :K) :
  embed (P.eval x)=afH P +
    ∑ n∈z4x width,ZC P (n+1)*asv x (n+1) := by
 have hd: (zcJ centre (P.map embed)).natDegree<width+1 := by
  rw [zQU]
  apply Polynomial.natDegree_map_le.trans_lt
  by_cases hzero :P=0
  · rw [hzero,Polynomial.natDegree_zero]
    exact Nat.zero_lt_succ width
  · exact (z2f hzero).mpr hP
 calc
  _=(zcJ centre (P.map embed)).eval (embed x - centre) := by
    rw [Polynomial.taylor_eval_sub,Polynomial.eval_map_apply]
  _ = _:= by
    rw [Polynomial.eval_eq_sum_range' hd,Finset.sum_range_succ']
    simp only [zPh,cMM,zJx,zqe]
    rw [zV7]
    refine zPw (fun s :kB=>afH P+s) (zUo rfl ?_)
    intro n hn
    apply gAQ
    have hn' := Finset.mem_range.mp hn
    change n<131071 at hn'
    change n+1<2130706433
    omega
private abbrev separant (g:af) :ko:=bC (dy g)
private def bhR (g:af) (x :K) :ko :=
  separant g^ahp*z9v 0 +
    ∑ n∈z4x width,
      separant g^(ahp-(2*n+1))*bC (numerator g n) *
        znf (asv x (n+1))
private def received (u:e9) (i:I) :ko :=
 znf (embed (u 0 i))+MvPolynomial.X 1*znf (embed (u 1 i))
private def D4 (u:e9) (g:af) (i:I) :ko :=
 bhR g (node i) - separant g^ahp*received u i
private theorem ctv (f :af) : (bC f).totalDegree≤f.totalDegree := by
 rw [totalDegree_eq,totalDegree_eq]
 exact zRS (z88 afH f)
private theorem cay {n:ℕ} (hn:n∈z4x width) :
  2*n+1≤ahp:= by
 have hn' := Finset.mem_range.mp hn
 unfold width at hn'
 unfold ahp width
 omega
private theorem c7v (u:e9) (i:I) : (received u i).totalDegree≤1 := by
 unfold received
 apply (totalDegree_add _ _).trans
 rw [totalDegree_C,Nat.zero_max]
 exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,totalDegree_C])
private theorem aC5 (f :af) (γ:K) (P:K[X]) :
  zY9 (point γ P) (bC f)=afH (OT f γ P) := by
 rw [bC,znM]
 exact (z6r afH (jW γ P) f).symm
private theorem d2X (g:af) (γ:K) (P:K[X])
   (hg:OT g γ P=0) (hP:P.degree<131072) (x :K) :
   zY9 (point γ P) (bhR g x) =
     afH (OT (dy g) γ P)^ahp*embed (P.eval x) := by
 let a :=afH (OT (dy g) γ P)
 simp only [bhR,zrl,zok,zkq,zdo,zV6,
   z9X,aC5]
 change a^ahp*afH P+(∑ n∈z4x width,
   a^(ahp-(2*n+1))*afH (OT (numerator g n) γ P) *
     asv x (n+1))=a^ahp*embed (P.eval x)
 rw [bds P hP,mul_add,zxw]
 refine zPw (fun s :kB=>a^ahp*afH P+s) (zUo rfl ?_)
 intro n hn
 rw [b12 g γ P hg,zok,zkq]
 change a^(ahp-(2*n+1))*(a^(2*n+1)*ZC P (n+1)) *
   asv x (n+1)=a^ahp*(ZC P (n+1)*asv x (n+1))
 rw [← ztg (a^(ahp-(2*n+1))),ztg _ (ZC P (n+1)),
   ← pow_add,zxt (cay hn)]
private theorem bFt (u:e9) (g:af) (γ:K) (P:K[X])
   (hg:ae8 g γ P) (hP:P.degree<131072) (i:I) :
   zY9 (point γ P) (D4 u g i)=0 ↔
     P.eval (node i)=u 0 i+γ*u 1 i:= by
 have hsep:afH (OT (dy g) γ P)≠0 :=
   (zw1 afH (zxb K[X] kB)).mpr hg.2
 have hreceived :zY9 (point γ P) (received u i) =
     embed (u 0 i+γ*u 1 i) := by
   simp only [received,zrl,zok,z9X,zV6,
     show point γ P 1=embed γ from rfl]
 rw [D4,zpO,zok,zkq,d2X g γ P hg.1 hP,
   aC5,hreceived,← mul_sub,mul_eq_zero,or_iff_right (zm1 _ hsep),
   sub_eq_zero]
 exact embed.injective.eq_iff
end
end bzp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace dm4
noncomputable section
open K1 BN agK MvPolynomial
open scoped Polynomial
section Regroup
variable {L:Type*} [za6 L]
private def aXA:z3y (Fin 2) L →+* z3y (Fin 3) L[X] :=
 (zHw (Fin.succ:Fin 2→Fin 3)).toRingHom.comp (zDK z1z)
private def Wn:z3y (Fin 2) (z3y (Fin 2) L) →+*
  z3y (Fin 3) L[X] :=
 zOD aXA ![C z7y,z9v 0]
private theorem dcT (a :z3y (Fin 2) L) :
  (aXA a).totalDegree≤a.totalDegree := by
 change (zHw Fin.succ (zDK z1z a)).totalDegree≤a.totalDegree
 exact (totalDegree_rename_le _ _).trans (zRS (z88 _ _))
end Regroup
section Specialize
variable {R:Type*} [za6 R]
private def specialize (s t:R) :z3y (Fin 3) R →+* R[X] :=
 zOD z1z ![z7y,z1z s,z1z t]
private theorem b17 (g:z3y (Fin 3) R) (s t P:R) :
  (specialize s t g).eval P=zY9 ![P,s,t] g:= by
 have h: (zhy P).comp (specialize s t) =
    zY9 ![P,s,t] := by
  apply zXT
  · intro a
    simp [specialize]
  · intro i
    fin_cases i <;> simp [specialize]
 exact zLs h g
private theorem cqs (g:z3y (Fin 3) R) (s t:R) :
    specialize s t (zWe 0 g)=zst (specialize s t g) := by
  classical
  induction g using z5i with
  | C a=>simp [specialize,Polynomial.derivative_C]
  | add f g hf hg=>simp only [map_add,hf,hg]
  | mul_X f i hf =>
    have hx :specialize s t (zWe 0 (z9v i)) =
        zst (specialize s t (z9v i)) := by
      fin_cases i <;> simp [specialize,zJH,zBT]
    simp only [Derivation.leibniz,zs5,zrl,zok,hf,hx,
      zAg]
    ac_rfl
private theorem cqp (s t:R) (g:z3y (Fin 3) R) (j:ℕ) :
   specialize s t ((zWe (R:=R) (0:Fin 3))^[j] g) =
    zst^[j] (specialize s t g) := by
 induction j with
 | zero=>rfl
 | succ j ih=>simp only [Function.iterate_succ_apply',cqs,ih]
end Specialize
section DecoderView
variable {L:Type*} [za6 L]
private def aHw:z3y (Fin 2) L →+* L[X][X] :=
 (zhd (zpe L (Fin 1)).toRingHom).comp
   ((z8s L 1).toRingHom.comp (zHw (z8T :Fin 2→Fin 2)).toRingHom)
private theorem bDW :
    (aHw (L:=L))=zOD (Polynomial.C.comp z1z)
      ![z1z z7y,z7y] := by
  apply zXT
  · intro a
    simp [aHw,zyf,uniqueAlgEquiv_apply]
  · intro i
    fin_cases i <;> rw [zrD]
    · have hx :z8s L 1 (zHw z8T (z9v (0:Fin 2))) =
          z1z (z9v (0:Fin 1)) := by
        rw [rename_X,show Fin.rev (0:Fin 2)=Fin.succ (0:Fin 1) by rfl,
          z07]
      change (z8s L 1 (zHw z8T (z9v (0:Fin 2)))).map
        (zpe L (Fin 1)).toRingHom=z1z z7y
      rw [hx]
      simp [uniqueAlgEquiv_apply]
    · have hx :z8s L 1 (zHw z8T (z9v (1 :Fin 2))) =
          Polynomial.X:= by
        rw [z6l,show z8T (1 :Fin 2)=0 by rfl,zOO]
      change (z8s L 1 (zHw z8T (z9v (1 :Fin 2)))).map
        (zpe L (Fin 1)).toRingHom=z7y
      rw [hx,zSo]
private theorem cJI:zq4 (aHw (L:=L)) :=
 (zTo _ (zpe L (Fin 1)).injective).comp
   ((z8s L 1).injective.comp (rename_injective _ zhY))
private theorem cJH (v :z3y (Fin 2) L) :
  (aHw v).natDegree≤v.degreeOf 1 := by
 change ((z8s L 1 (zHw z8T v)).map _).natDegree≤v.degreeOf 1
 apply Polynomial.natDegree_map_le.trans
 rw [natDegree_finSuccEquiv,← show z8T (1 :Fin 2)=0 by rfl]
 exact (degreeOf_rename_of_injective zhY 1).le
private theorem dfa (v :z3y (Fin 2) (z3y (Fin 2) L))
   (s t:L) :
   specialize (z1z s) (z1z t) (Wn v) =
     aHw (v.map (zY9 ![s,t])) := by
 let Kw:z3y (Fin 2) L →+* L:=zY9 ![s,t]
 have hseed : (specialize (z1z s) (z1z t)).comp aXA =
     (Polynomial.C.comp z1z).comp Kw:= by
   apply zXT
   · intro a
     simp [specialize,aXA,Kw]
   · intro i
     fin_cases i <;> simp [specialize,aXA,Kw]
 have h: (specialize (z1z s) (z1z t)).comp Wn =
     aHw.comp (zDK Kw) := by
   apply zXT
   · intro a
     simpa [Wn,bDW,zQb] using zLs hseed a
   · intro i
     fin_cases i <;> simp [Wn,specialize,bDW]
 exact zLs h v
private theorem cMS (v :z3y (Fin 2) L) (P:L[X]) :
  (aHw v).eval P=zIe ![z7y,P] v := by
 have h: (zhy P).comp aHw =
    (zIe ![z7y,P]).toRingHom:= by
  apply zXT
  · intro a
    simp [bDW]
  · intro i
    fin_cases i <;> simp [bDW]
 exact zLs h v
end DecoderView
open Polynomial in
private theorem cNH {R:Type*} [za6 R] [IsDomain R]
   (q B:ℕ) [CharP R q] (f :R[X]) (hf :f≠0) (hdegree :f.natDegree≤B)
   (hsmall:B<q) (y :R) (hroot :f.IsRoot y) :
   ∃ j<B,(zst^[j] f).IsRoot y ∧
     ¬ (zst (zst^[j] f)).IsRoot y := by
 let μ:=f.rootMultiplicity y
 have hμpos :0<μ:=(rootMultiplicity_pos hf).mpr hroot
 have hμle :μ≤B:= by
   have hd:=zkM (f.pow_rootMultiplicity_dvd y) hf
   have hle :μ≤f.natDegree := by simpa [μ,natDegree_pow] using hd
   exact hle.trans hdegree
 have hnzd : ∀ m≤μ,m≠0→(m:R)∈zgt R:= by
   intro m hm hmn
   apply mem_nonZeroDivisors_of_ne_zero
   intro hz
   have hd:q∣m:=(zX2 R q m).mp hz
   have hq:q≤ m:=zTm (Nat.pos_of_ne_zero hmn) hd
   omega
 have hnext : ¬ (zst^[μ] f).IsRoot y := by
   intro hnext
   have hall : ∀ m≤μ,(zst^[m] f).IsRoot y := by
     intro m hm
     rcases lt_or_eq_of_le hm with hh | rfl
     · exact zz7 hh
     · exact hnext
   exact (Nat.lt_irrefl μ)
     (lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hf hall hnzd)
 refine ⟨μ - 1,by omega,zz7 (by omega),?_⟩
 have he :zst (zst^[μ - 1] f)=zst^[μ] f := by
   simpa only [Nat.succ_eq_add_one,zxt hμpos] using
     (zLk zst (μ - 1) f).symm
 rwa [he]
end
end dm4
end
section
namespace Qt
noncomputable section
open cu Polynomial MvPolynomial
private abbrev Flat :=z3y (Option (Fin 2)) FX
private def flatten:zS3 ≃ₐ[FX] Flat :=(optionEquivLeft FX (Fin 2)).symm
private def AV:zS3 ≃ₐ[FX] z3y (Fin 2) FX[X] :=
 flatten.trans (optionEquivRight FX (Fin 2))
def gY (f :zS3) :ℕ:=(AV f).totalDegree
private theorem bNI (f :zS3) (i:ℕ) (d:Fin 2 →₀ ℕ) :
  ((AV f).coeff d).coeff i=(f.coeff i).coeff d:= by
 change ((optionEquivRight FX (Fin 2) (flatten f)).coeff d).coeff i= _
 rw [optionEquivRight_coeff_coeff,← optionEquivLeft_coeff_coeff]
 simp [flatten]
theorem Qc (f :zS3) (u:ℕ) :
   gY f≤u↔vm f u:= by
 unfold gY vm
 simp only [MvPolynomial.totalDegree,Finset.sup_le_iff]
 constructor
 · intro h i d hd
   apply h d
   rw [zuk] at hd ⊢
   intro hz
   apply hd
   rw [← bNI,hz,zO6]
 · intro h d hd
   obtain ⟨i,hi⟩:=Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
   apply h i d
   rwa [zuk,← bNI,← Polynomial.mem_support_iff]
theorem acG {f g:zS3} (hf :f≠0) (hg:g≠0) :
  gY (f * g)=gY f+gY g:= by
 unfold gY
 rw [zok,totalDegree_mul_of_isDomain (by simpa using hf) (by simpa using hg)]
theorem bg4 {f :zS3} (hf :f≠0) (n:ℕ) :
   gY (f^n)=n*gY f := by
 induction n with
 | zero=>simp [gY]
 | succ n ih=>rw [pow_succ,acG (pow_ne_zero _ hf) hf,ih,Nat.succ_mul]
private theorem b3z {g:zS3} {a u:ℕ}
  (ha :g.natDegree≤a) (hu:gY g≤u) :
  flatten g∈restrictBidegree (Fin 2) FX a u:= by
 rw [mem_restrictBidegree]
 intro d hd
 have hy :d none≤(flatten g).degreeOf none := by
  rw [degreeOf_eq_sup]
  exact zZi (f := fun d:Option (Fin 2) →₀ ℕ=>d none) hd
 have hyeq :=natDegree_optionEquivLeft FX (flatten g)
 have hy' : d none≤g.natDegree :=hy.trans_eq (by simpa [flatten] using hyeq.symm)
 have hs :=le_weightedTotalDegree (fun v :Option (Fin 2) ↦ v.elim 0 fun _ ↦ 1) hd
 rw [Finsupp.weight_elim_zero_one,← totalDegree_optionEquivRight] at hs
 exact ⟨hy'.trans ha,hs.trans hu⟩
end
end Qt
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 850000
namespace aFX
noncomputable section
open K1 cu gT pI Ty Polynomial
open scoped Classical
private def unflatten:z87 →+* Jet :=
 zOD (C.comp (C.comp znf))
  ![C (C (z9v 0)),C (C (z9v 1)),
    C (z7y (R:=aZ)),z7y (R:=zS3)]
private theorem to_from:iJ.comp unflatten=zz5 Ambient:= by
 apply zXT
 · intro c
   simp [unflatten,iJ,A7,oi,pZ]
 · intro i
   fin_cases i <;> simp [unflatten,iJ,A7,oi,pZ]
private theorem from_to :unflatten.comp iJ=zz5 Jet:= by
  apply z86
  · intro f
    suffices h: (unflatten.comp iJ).comp C=(zz5 Jet).comp C from
      zmU h f
    apply z86
    · intro a
      suffices h: ((unflatten.comp iJ).comp C).comp C =
          ((zz5 Jet).comp C).comp C from zmU h a
      apply zXT
      · intro c
        simp [unflatten,iJ,A7,oi,pZ]
      · intro i
        fin_cases i <;> simp [unflatten,iJ,A7,oi,pZ]
    · simp [unflatten,iJ,A7,oi,pZ]
  · simp [unflatten,iJ]
theorem gBO {P Q:Jet} (h:XY.ag6 P Q) :
    zRK (iJ P) (iJ Q) := by
  have hrel :zRK P Q:=WfDvdMonoid.isRelPrime_of_no_irreducible_factors
    (fun hp=>h.left_ne hp.1) (fun d hi hd=>h.no_common d hi hd)
  intro d hdP hdQ
  have un (a :Jet) :unflatten (iJ a)=a :=zmU from_to a
  have hd:zWB (unflatten d) :=
    hrel (by simpa only [un] using map_dvd unflatten hdP)
         (by simpa only [un] using ztu unflatten hdQ)
  have hD:iJ (unflatten d)=d:=zmU to_from d
  rw [← hD]
  exact hd.map iJ
private theorem acI (f :zS3) (i:ℕ) :
   (f.coeff i).totalDegree≤gY f := by
 by_cases h:i∈f.support
 · exact zZi (f := fun j=>(f.coeff j).totalDegree) h
 · simp [Polynomial.notMem_support_iff.mp h]
private theorem dtm (f :zS3) :gY f= Qt.gY f := by
 apply zWs
 · exact Finset.sup_le fun i _=>(Qt.Qc f _).mp le_rfl i
 · exact (Qt.Qc f _).mpr (acI f)
private def bem (f :zS3) (j:ℕ) :Shape :=⟨1,f.natDegree,j,gY f⟩
private theorem aUy (f :zS3) (j:ℕ) :oU (C f) (bem f j) := by
 intro v y hy
 cases v with
 | zero =>
   rw [coeff_C_zero] at hy ⊢
   exact ⟨by simpa [bem] using zZI hy,zD0 _,acI _ _⟩
 | succ v=>simp [coeff_C_succ] at hy
private theorem order_one {I:znc z87} {P:Jet} (hi:I.IsPrime) (h:iJ P∈I) :
  O9 I P 1 := by
 refine ⟨1,hi.one_notMem,?_⟩
 rw [one_mul,pow_one]
 exact zKg h
private theorem ekt (lengths :Ty.c4) (sections :Ty.c5)
    {P Q:Jet} {f :zS3} (hf :z5o f) (hpos :0<f.natDegree)
    (hsmall:f.natDegree<p) (hP:C f∣P) (hQ:C f∣Q)
    (S:zJe (znc z87))
    (hS : ∀ I∈S,xN I∧aTw P Q I∧iJ (C f)∈I) (k :Fin 4) :
    mass S k≤aaW (gY f) f.natDegree k := by
  obtain ⟨g,a,ha,hp,_⟩:=YZ.c2P f hf hpos hsmall
  have hc:oU (YZ.alD g) (bem f 1) :=
    YZ.bWO hp.left_ne (aUy f 1) le_rfl (dvd_refl _) ha
  have h:=sections (C f) (YZ.alD g) (bem f 0) (bem f 1)
    S k 1 hp.left_ne hp.right_ne (gBO hp) (zD0 _) hpos (aUy f 0) hc
    (by decide) (by
      intro I hI
      obtain ⟨active,comp,hon⟩:=hS I hI
      have hc' := comp f hf hpos hP hQ hon g a ha
      refine ⟨active,fun _ => ?_⟩
      simpa using lengths _ _ I active 1 (by decide)
        (order_one active.prime hon) (order_one active.prime hc'))
  fin_cases k <;> simpa [bem,aoD,aaW,two_mul,Nat.add_mul] using h
private theorem emI (x z y w:ℕ) (k :Fin 4) :
  aaW x z k+aaW y w k≤aaW (x+y) (z+w) k := by
 fin_cases k <;> simp [aaW] <;> nlinarith
private theorem emP (r x z :ℕ) (k :Fin 4) :
  aof r k * aaW x z k=aaW (r*x) (r*z) k := by
 fin_cases k <;> simp [aaW,aof] <;> ring
private theorem bWc {R:Type*} [CommMonoidWithZero R] [zsh R]
  {e f T:R} {r :ℕ} (h:zRK e f) (hd:e^r∣f^r*T) :e^r∣T :=
 h.pow.dvd_of_dvd_mul_left hd
private theorem fWH {e f T:zS3} {r :ℕ} (h:zRK e f)
  (hd:e^r∣f^r*T) :e^r∣T:= by
 let:zsh FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
 let:zsh aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 let:zsh Equation :=Polynomial.uniqueFactorizationMonoid
 exact bWc h hd
theorem cUH (lengths :Ty.c4) (sections :Ty.c5)
    (H :zS3) (P Q:Jet) (S:zJe (znc z87)) (r :ℕ)
    (hH :H≠0) (hp:H.natDegree<p) (hr :0< r)
    (hP:C H∣P) (hQ:C H∣Q)
    (hS : ∀ I∈S,xN I∧aTw P Q I∧aYS H r I) (k :Fin 4) :
    aof r k*mass S k≤aaW (gY H) H.natDegree k := by
  classical
  by_cases hs :S.Nonempty
  · obtain ⟨I,hI⟩:=hs
    obtain ⟨f,hf,hpos,hpow,_⟩:=(hS I hI).2.2
    obtain ⟨T,hfac⟩:=hpow
    have hT:T≠0:= by
      intro hz
      exact hH (by simp [hfac,hz])
    have hdeg:H.natDegree=r*f.natDegree+T.natDegree := by
      rw [hfac,natDegree_mul (zm1 _ hf.ne_zero) hT,natDegree_pow]
    have hseed :gY H=r*gY f+gY T:= by
      simp only [dtm,hfac,Qt.acG (zm1 _ hf.ne_zero) hT,
        Qt.bg4 hf.ne_zero]
    have hfd:f∣H :=(dvd_pow_self f hr.ne').trans ⟨T,hfac⟩
    have hTd:T∣H :=⟨f^r,hfac.trans (zDE _ _)⟩
    let on (J:znc z87) :=iJ (C f)∈J
    have hg:=ekt lengths sections hf hpos ((zkM hfd hH).trans_lt hp)
      ((ztu (C:zS3 →+* Jet) hfd).trans hP) ((ztu (C:zS3 →+* Jet) hfd).trans hQ) (S.filter on)
      (fun J hJ=> by
        obtain ⟨hm,ho⟩:=Finset.mem_filter.mp hJ
        exact ⟨(hS J hm).1,(hS J hm).2.1,ho⟩) k
    have ht:=cUH lengths sections T P Q (S.filter fun J => ¬ on J) r hT
      ((zkM hTd hH).trans_lt hp) hr
      ((ztu (C:zS3 →+* Jet) hTd).trans hP) ((ztu (C:zS3 →+* Jet) hTd).trans hQ) (by
        intro J hJ
        obtain ⟨hm,ho⟩:=Finset.mem_filter.mp hJ
        obtain ⟨active,comp,e,he,hy,hd,hmem⟩:=hS J hm
        have hcop:zRK e f :=he.isRelPrime_iff_not_dvd.mpr (by
          rintro ⟨b,hb⟩
          apply ho
          change iJ (C f)∈J
          rw [hb,zok,zok]
          exact J.mul_mem_right _ hmem)
        refine ⟨active,comp,e,he,hy,fWH hcop ?_,hmem⟩
        simpa only [← hfac] using hd) k
    have hadd:mass (S.filter on) k+mass (S.filter fun J => ¬ on J) k=mass S k :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [← hadd,Nat.mul_add,hseed,hdeg]
    exact (Nat.add_le_add (Nat.mul_le_mul_left _ hg) ht).trans
      (by rw [emP]; exact emI _ _ _ _ _)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs,mass]
termination_by H.natDegree
decreasing_by
 have hpos' := Nat.mul_pos hr hpos
 omega
end
end aFX
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace aqb
noncomputable section
open K1 cu gT pI Ty Polynomial
open scoped nonZeroDivisors
private theorem dcG (f :zS3) :gY f= Qt.gY f := by
 apply zWs
 · refine Finset.sup_le fun j _ => ?_
   exact ((Qt.Qc _ _).mp le_rfl) j
 · apply (Qt.Qc _ _).mpr
   intro j
   by_cases hj:f.coeff j=0
   · simp [hj]
   · exact zZi (f := fun j=>(f.coeff j).totalDegree) (mem_support_iff.mpr hj)
private theorem gn4 {f H :zS3} (hH :H≠0) (h:f∣H) :
  gY f≤gY H := by
 obtain ⟨g,rfl⟩:=h
 rw [dcG,dcG,
  Qt.acG (z67 hH) (right_ne_zero_of_mul hH)]
 exact z8K _ _
private theorem goS (a :aZ) :
    Dk (Co (C a))=znf (z12 aZ aQ a) := by
  have he :Dk.comp (oi.comp pZ) =
      MvPolynomial.C.comp (z12 aZ aQ) := by
    apply zXT
    · intro c
      simp only [zQb,oi,pZ,ziQ,
        zlv,MvPolynomial.rename_C,Dk,zTv]
      rw [zG3 FX aZ aQ,zKm]
    · intro i
      fin_cases i <;> simp [oi,pZ,Dk,ek]
  simpa [iJ,A7] using zLs he a
private theorem ddc {I:znc z87} (hI:xN I) {a :aZ}
   (ha :a≠0) :Co (C a)∉I:= by
 intro h
 have hunit :zWB (Dk (Co (C a))) := by
   rw [goS]
   exact (isUnit_iff_ne_zero.mpr (fun hz=>ha ((zxb _ _)
     (hz.trans (zhc (z12 aZ aQ)).symm)))).map
     znf
 have htop:I.map Dk = ⊤ :=
   Ideal.eq_top_of_isUnit_mem _ (z7X _ h) hunit
 let:Subsingleton (Y0 I) :=Ideal.Quotient.subsingleton_iff.mpr htop
 exact hI.seed_size.1.ne' (z6g aQ (Y0 I))
attribute [local instance] Polynomial.algebra in
theorem eHG {I:znc z87} (hI:xN I)
   (hP:I.comap Co ≠ ⊥) :
   ∃ f :zS3,z5o f∧0<f.natDegree ∧
     I.comap Co=zye {f} := by
 let P:znc Equation :=I.comap Co
 have :I.IsPrime :=hI.prime
 have :P.IsPrime :=Ideal.comap_isPrime Co I
 let S:Submonoid Equation :=(zgt aZ).map (C:aZ →+* zS3)
 have :=Polynomial.isLocalization (zgt aZ) aQ
 have hdisj:Disjoint (S:Set zS3) (P:Set zS3) := by
   rw [Set.disjoint_left]
   rintro _ ⟨a,ha,rfl⟩ h
   exact ddc hI (mem_nonZeroDivisors_iff_ne_zero.mp ha) h
 let Q:=P.map (z12 zS3 aQ[X])
 have :Q.IsPrime :=
   znL S aQ[X] P inferInstance hdisj
 have hle :=Ideal.height_le_ringKrullDim_of_isPrime (I:= Q)
 have hdim:ringKrullDim aQ[X]=1 := by simp [ringKrullDim_eq_zero_of_field]
 rw [hdim] at hle
 have hheight:zmO (R:=aQ[X]) Q=zmO (R:=zS3) P :=
   IsLocalization.height_map_of_disjoint (R:=zS3) (S:=aQ[X]) S P hdisj
 have hle' : zmO (R:=zS3) P≤1 :=
   hheight ▸ WithBot.coe_le_coe.mp hle
 have hge :1≤zmO (R:=zS3) P:= by
   have hlt: (⊥ : znc zS3)<P:=bot_lt_iff_ne_bot.mpr hP
   simpa using Ideal.height_add_one_le_of_lt_of_isPrime hlt
 obtain ⟨f,hf⟩:=(UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (p:=P)
   (zWs hle' hge)).principal
 change P=zye {f} at hf
 have hf0:f≠0:= by
   intro h
   exact hP (by simpa [h] using hf)
 have hprime : (zye ({f} : Set zS3)).IsPrime := by
   rw [← hf]
   infer_instance
 have hmem:Co f∈I:= by
   change f∈P
   rw [hf]
   exact z5J f
 have hdeg:0<f.natDegree := by
   by_contra! h
   have hfC:=eq_C_of_natDegree_eq_zero (za7 h)
   exact ddc hI (fun hz=>hf0 (hfC.trans (by rw [hz,map_zero])))
     (hfC ▸ hmem)
 exact ⟨f,((Ideal.span_singleton_prime hf0).mp hprime).irreducible,hdeg,hf⟩
theorem eHJ {I:znc z87} (hI:xN I) {H :zS3} (hH :H≠0)
   {r :ℕ} (hhigh : ¬ aYS H r I) (hmem:Co H∈I) :
   ∃ (f g:zS3) (e :ℕ),H=f^e*g∧e< r ∧
     z5o f∧0<f.natDegree∧f.natDegree≤H.natDegree ∧
     gY f≤gY H∧I.comap Co=zye {f} ∧
     Co g∉I:= by
 have hP:I.comap Co ≠ ⊥ := by
   intro hp
   change H∈I.comap Co at hmem
   exact hH (Ideal.mem_bot.mp (hp ▸ hmem))
 obtain ⟨f,hf,hpos,hcontract⟩:=eHG hI hP
 have hfI:Co f∈I:= by
   change f∈I.comap Co
   rw [hcontract]
   exact z5J f
 have hnot : ¬ f^r∣H := fun h=>hhigh ⟨f,hf,hpos,h,hfI⟩
 have hdvd:f∣H := by
   change H∈I.comap Co at hmem
   rwa [hcontract,zxV] at hmem
 classical
 let ex : ∃ n:ℕ,¬ f^n∣H :=⟨r,hnot⟩
 have hminpos :0<Nat.find ex := by
   by_contra! h
   have hn:=Nat.find_spec ex
   rw [za7 h,zJx] at hn
   exact hn (one_dvd _)
 obtain ⟨e,he⟩:=zwS hminpos.ne'
 have her :e< r := by
   have hh:=Nat.find_min' ex hnot
   omega
 have hediv :f^e∣H := by
   by_contra hn
   exact Nat.find_min ex (show e<Nat.find ex by omega) hn
 obtain ⟨g,hg⟩:=hediv
 refine ⟨f,g,e,hg,her,hf,hpos,zkM hdvd hH,
   gn4 hH hdvd,hcontract,?_⟩
 intro hgI
 change g∈I.comap Co at hgI
 rw [hcontract,zxV] at hgI
 obtain ⟨v,hv⟩:=hgI
 apply Nat.find_spec ex
 use v
 rw [he,pow_succ,hg,hv,ztg]
end
end aqb
end
section
namespace Qt
noncomputable section
open cu Polynomial Finset
section Filtration
variable {F A:Type*} [zrb F] [za6 A] [zZE F A]
private def filtered (V:zpI F A[X]) (n:ℕ) :zpI F A[X] :=
 V ⊓ (degreeLT A n).restrictScalars F
private theorem Wb {V:zpI F A[X]} {P:A[X]} {n:ℕ} :
  P∈filtered V n↔P∈V∧P.degree<n :=
 and_congr_right fun _=>mem_degreeLT
private def bek (V:zpI F A[X]) (j:ℕ) :
   filtered V (j+1) →ₗ[F] A :=
 ((lcoeff A j).restrictScalars F).comp (filtered V (j+1)).subtype
private theorem eiD (V:zpI F A[X]) (j:ℕ) :
    z1x F (bek V j).ker=z1x F (filtered V j) := by
  have heq : (bek V j).ker.map (filtered V (j+1)).subtype=filtered V j:= by
    apply Submodule.ext
    intro P
    constructor
    · rintro ⟨⟨Q,hQ⟩,hker,rfl⟩
      obtain ⟨hV,hd⟩:=Wb.mp hQ
      refine Wb.mpr ⟨hV,(degree_lt_iff_coeff_zero _ _).2 ?_⟩
      intro i hi
      by_cases hij:i=j
      · subst i
        exact hker
      · exact (degree_lt_iff_coeff_zero _ _).1 hd i (by omega)
    · intro hP
      obtain ⟨hV,hd⟩:=Wb.mp hP
      have hP' : P∈filtered V (j+1) :=
        Wb.mpr ⟨hV,hd.trans (by norm_cast; omega)⟩
      exact ⟨⟨P,hP'⟩,coeff_eq_zero_of_degree_lt hd,rfl⟩
  rw [← heq,rank_map_eq (filtered V (j+1)).injective_subtype]
private theorem eay (V:zpI F A[X]) (g:ℕ→ℕ)
   (h : ∀ j,z1x F (bek V j).range≤(↑(g j) :Cardinal)) (n:ℕ) :
   z1x F (filtered V n)≤(↑(∑ j∈z4x n,g j) :Cardinal) := by
 induction n with
 | zero =>
   have hzero :filtered V 0 = ⊥ := by
     apply bot_unique
     intro P hp
     rw [Submodule.mem_bot]
     by_contra hn
     have h:=(z2f hn).2 (Wb.mp hp).2
     omega
   rw [hzero]
   simp
 | succ n ih =>
   rw [← (bek V n).rank_range_add_rank_ker,eiD,sum_range_succ,
     Nat.cast_add,zV7]
   exact add_le_add ih (h n)
private theorem bGH (V:zpI F A[X]) (g:ℕ→ℕ) (n:ℕ)
  (h : ∀ j,z1x F (bek V j).range≤(↑(g j) :Cardinal))
  (hdeg : ∀ P∈V,P.degree<n) :
  zsE F V ≤ ∑ j∈z4x n,g j:= by
 have heq :filtered V n=V :=
  inf_eq_left.mpr fun P hp=>mem_degreeLT.mpr (hdeg P hp)
 have hr :=eay V g h n
 rw [heq] at hr
 exact Module.finrank_le_of_rank_le hr
end Filtration
end
end Qt
end
section
namespace aKv
noncomputable section
open wH
def minPrimes (J:znc zza) :zJe (zy6 zza) :=
  ((J.finite_minimalPrimes_of_isNoetherianRing).preimage
    (f :=PrimeSpectrum.asIdeal) (by
      intro p _ q _ hpq
      exact PrimeSpectrum.ext_iff.mpr hpq)).toFinset
@[simp] theorem b8X (J:znc zza) (p:zy6 zza) :
   p∈minPrimes J↔p.asIdeal∈J.minimalPrimes :=
  Set.Finite.mem_toFinset _
def ah4 (J:znc zza) (q:zy6 zza) :
    zJe (zy6 zza) := by
  classical
  exact (minPrimes J).filter (fun p=>p.asIdeal≤q.asIdeal)
theorem aID (J:znc zza) (q p:zy6 zza) :
  p∈ah4 J q↔p.asIdeal∈J.minimalPrimes∧p.asIdeal≤q.asIdeal:= by
 classical
 rw [ah4,Finset.mem_filter,b8X]
def aB4 (q:zy6 zza) (J:znc zza) (t:zza) :Prop :=
 let A:=Localization.AtPrime q.asIdeal
 IsSMulRegular (A ⧸ J.map (z12 zza A)) (z12 zza A t)
end
end aKv
end
