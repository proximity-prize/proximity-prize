import ProximityPrize.SubmissionLower.J
import ProximityPrize.SubmissionLower.K
import ProximityPrize.SubmissionLower.B
set_option Elab.async false
set_option maxRecDepth 2000
set_option maxHeartbeats 1500000
open _root_ renaming AlgEquiv.apply_symm_apply → zIH, AlgEquiv.trans_apply → zfq, AlgHom.toLinearMap_apply → zJr, Algebra → zZE, Algebra.FiniteType → zUK, Algebra.FormallyEtale → zk2, Algebra.IsIntegral → zVK, Algebra.IsSeparable → zw7, Algebra.IsSeparable.isSeparable → zMb, Algebra.TensorProduct.quotIdealMapEquivTensorQuot → zeK, Algebra.algebraMap → z12, Algebra.finrank_eq_of_equiv_equiv → znv, Algebra.smul_def → zd5, B8.cylinder → zr0, CharP.cast_eq_zero_iff → zX2, CommRing → za6, DFunLike.congr_fun → zmU, DecidableEq → zRw, Derivation → zvY, Derivation.restrictScalars_apply → zNe, Derivation.smul_apply → zep, E7.CurvePlace → zGX, E7.poleOrder → zbb, Field → zrb, Fin.sum_univ_three → zCj, Fin.val → zf5, Finite → zTn, FiniteDimensional → zQO, Finset → zJe, Finset.HasAntidiagonal.antidiagonal → z5G, Finset.exists_mem_eq_sup → zOU, Finset.le_sup → zZi, Finset.mem_univ → zTc, Finset.one_le_prod₀ → z9l, Finset.prod_congr → zX3, Finset.range → z4x, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Finset.sum_eq_single_of_mem → zpa, Finset.sum_eq_zero → zYF, Finset.sum_le_sum → zQk, Finset.sum_mul → zkr, Finset.sum_range_succ → zpB, Finset.sum_sub_distrib → zQr, Finset.sup_le → zf9, Finset.univ → zdB, Finsupp.add_apply → zSs
open _root_ renaming Finsupp.degree_apply → zqc, Finsupp.equivFunOnFinite_symm_coe → zWu, Finsupp.erase_add_single → zop, Finsupp.mapDomain_apply_of_injective → zm3, Finsupp.single → zhf, Finsupp.single_apply → zoV, Finsupp.single_eq_pi_single → zsZ, Finsupp.weight → ztN, Finsupp.weight_apply → zDM, Finsupp.weight_eq_sum → z1K, Finsupp.weight_single → zTy, Fintype → z85, Fintype.card → zhP, Fintype.card_sigma → zTU, FractionRing → zNv, Function.Injective → zq4, Function.Surjective → zpX, Ideal → znc, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.factorₐ → z5F, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.comap_isPrime → zG1, Ideal.exists_minimalPrimes_le → zXL, Ideal.map_map → z0L, Ideal.map_span → zlN, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_right → zs1, Ideal.ofList → zGZ, Ideal.smul_eq_mul → zHM, Ideal.span → zye, Ideal.subset_span → zCn, Int.toNat_le_toNat → z0Z, Int.toNat_of_nonneg → zi4, IntermediateField.adjoin → zvb, IntermediateField.subset_adjoin → zmq, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.div_surjective → zJC, IsFractionRing.finrank_left_eq → z4U, IsFractionRing.injective → zxb, IsFractionRing.of_field → z6t, IsLeftRegular → zWc, IsLocalRing.maximalIdeal → zrY, IsLocalRing.residue → zeo, IsLocalization → zNo
open _root_ renaming IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes → z8P, IsLocalization.Away.invSelf → zdx, IsLocalization.Away.lift → ztx, IsLocalization.map_units → z0j, IsLocalization.surj → zg4, IsRelPrime → zRK, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.algebraMap_eq → zYY, IsScalarTower.of_algebraMap_eq → zsL, IsScalarTower.toAlgHom → zE2, Jq.Represents → zmV, Jq.squarefree → zu2, KaehlerDifferential.D → zOb, Kd.capMap → zxY, LinearMap.comp_apply → zoD, LinearMap.congr_fun → z5U, LinearMap.finrank_le_finrank_of_injective → zdv, LinearMap.ker → z83, LinearMap.mem_ker → zeS, LinearMap.mulLeft → zzN, LinearMap.range → zWl, List.ofFn → zUT, List.toFinset_card_of_nodup → zi0, Localization.AtPrime → zhy, Localization.AtPrime.map_eq_maximalIdeal → zRt, Module.Finite → zAa, Module.annihilator → zM2, Module.finrank → zsE, MulZeroClass.mul_zero → znR, MulZeroClass.zero_mul → z1S, Multiset.count_dedup → zKw, Multiset.count_nsmul → z5K, Multiset.filter_le → z7n, Multiset.le_iff_count → zyB, Multiset.mem_of_le → zvO, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.C_dvd_iff_dvd_coeff → zXG, MvPolynomial.C_mem_restrictJointDegree → z8b, MvPolynomial.X → z9v, MvPolynomial.X_mem_restrictWeightedOrder → z9j, MvPolynomial.aeval → zIe, MvPolynomial.aeval_X → zTw, MvPolynomial.affineDegree → zHf, MvPolynomial.affineHilbertFunction → ztr, MvPolynomial.affineHilbertPolynomial → zIU, MvPolynomial.algHom_ext → zpH
open _root_ renaming MvPolynomial.basisRestrictSupport → zzc, MvPolynomial.bind₁_mem_restrictWeightedOrder → zku, MvPolynomial.coeff_C_mul → z06, MvPolynomial.coeff_eq_zero_of_totalDegree_lt → zdp, MvPolynomial.coeff_map → zS3, MvPolynomial.coeff_monomial → z0I, MvPolynomial.coeff_mul → zcz, MvPolynomial.coeff_sum → zqN, MvPolynomial.eq_affineHilbertPolynomial_of_eval_eq → zpC, MvPolynomial.eval → zY9, MvPolynomial.eval_map → znM, MvPolynomial.eval₂ → zSZ, MvPolynomial.eventually_eval_affineHilbertPolynomial → zaL, MvPolynomial.exists_eval_affineHilbertPolynomial → zQf, MvPolynomial.finSuccEquiv → z8s, MvPolynomial.hom_eval₂ → zUe, MvPolynomial.homogeneousComponent → zyc, MvPolynomial.homogeneousComponent_eq_self → zoF, MvPolynomial.homogeneousComponent_eq_zero → znu, MvPolynomial.homogeneousComponent_isHomogeneous → z8k, MvPolynomial.map → zDK, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.mem_restrictTotalDegree → zpJ, MvPolynomial.mem_support_iff → zuk, MvPolynomial.mk_mem_quotientDegreeLE → ziU, MvPolynomial.monomial → ztt, MvPolynomial.monomial_mul_monomial → zDU, MvPolynomial.monomial_pow → zpV, MvPolynomial.mul_mem_quotientDegreeLE → zan, MvPolynomial.mul_mem_restrictWeightedOrder → zgN, MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le → zy5, MvPolynomial.pderiv → zWe, MvPolynomial.pderiv_X → zYE, MvPolynomial.quotientDegreeLE → z9e, MvPolynomial.quotientDegreeLE_mono → zhv, MvPolynomial.renameEquiv → zGY, MvPolynomial.renameEquiv_apply → zyk, MvPolynomial.restrictJointDegree → zgW, MvPolynomial.restrictSupport → zQW, MvPolynomial.restrictTotalDegree → z0U, MvPolynomial.restrictWeightedOrder → zlK, MvPolynomial.restrictWeightedOrder_anti → z2F, MvPolynomial.ringHom_ext → zXT, MvPolynomial.sum_homogeneousComponent → zjO, MvPolynomial.totalDegree_mul → zhM, MvPolynomial.uniqueAlgEquiv → zpe, MvPolynomial.weightedTotalDegree → zXg
open _root_ renaming MvPolynomial.weightedTotalDegree_le_of_dvd → zJD, MvPolynomial.weightedTotalDegree_one → zBy, Nat.add_comm → zg2, Nat.add_le_add_left → z3b, Nat.add_sub_cancel → z2h, Nat.cast_add → z6H, Nat.cast_mul → z2R, Nat.cast_one → z4o, Nat.cast_sub → zjK, Nat.cast_succ → zg0, Nat.cast_sum → zCt, Nat.cast_zero → zQq, Nat.choose_one_right → zk3, Nat.choose_two_right → zzd, Nat.eq_zero_of_le_zero → za7, Nat.factorial_succ → zwO, Nat.lt_succ_of_le → zB1, Nat.mul_comm → z5A, Ne.symm → z9m, Option → zNO, Polynomial → zM1, Polynomial.Bivariate.swap → zwz, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.X_ne_zero → z05, Polynomial.aeval → zEU, Polynomial.aeval_C → z8q, Polynomial.aeval_def → zCD, Polynomial.algEquivOfTranscendental → zjm, Polynomial.algebra → z87, Polynomial.algebraMap_def → zeg, Polynomial.algebraMap_eq → zrD, Polynomial.backwardDifference → zW9, Polynomial.coe_mapRingHom → zKC, Polynomial.coeff_add → z7l, Polynomial.coeff_eq_zero_of_natDegree_lt → zQl, Polynomial.coeff_zero → zO6, Polynomial.derivative → zst, Polynomial.evalRingHom → zhz, Polynomial.eval_C → zFf, Polynomial.eval_add → zvF, Polynomial.eval_map_apply → zdm, Polynomial.eval₂RingHom → zqf, Polynomial.finsetSum_coeff → zaW, Polynomial.hasseDeriv → z75, Polynomial.hasseDeriv_map → zvc, Polynomial.hom_eval₂ → zly, Polynomial.induction_on' → zCU
open _root_ renaming Polynomial.isLocalization → zyz, Polynomial.leadingCoeff → z4w, Polynomial.map → zGG, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.map_id → zeh, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.map_monomial → zAZ, Polynomial.map_pow → z5m, Polynomial.map_zero → zgY, Polynomial.modByMonic_eq_zero_iff_dvd → zNp, Polynomial.natDegree_C → zti, Polynomial.natDegree_hasseDeriv_le → zax, Polynomial.ringHom_ext → z86, PolynomialDifferential.differentialSpecialization → zho, PolynomialDifferential.separant → z92, PolynomialDifferential.taylorExponentSufficient_firstOrder_tight → zH5, RatFunc → ziC, RatFunc.C → ztW, RatFunc.X → zyX, RatFunc.algebraMap_C → zyJ, RatFunc.algebraMap_X → zYR, RatFunc.algebraMap_eq_C → z4W, RatFunc.induction_on → zSH, RingHom.algebraMap_toAlgebra → zy4, RingHom.comp_apply → zQb, RingHom.comp_assoc → zxS, RingHom.ext → zz5, RingHom.id → zz4, RingHom.ker → zdq, RingHom.mem_ker → zry, Rj.offset → zve, Set.image_singleton → zyl, Set.mem_ofPred_eq → zsi, Set.mem_singleton → zT1, Subalgebra.inclusion → zDu, Subfield.subset_closure → zfX, Submodule.add_mem → zcy, Submodule.equivMapOfInjective → zW6, Submodule.map_span → zYZ, Submodule.span_induction → zt0, Submodule.sub_mem → zMG, Submodule.subset_span → zBO, Submodule.sum_mem → zo3, Submodule.zero_mem → z4M, Submonoid → zdT
open _root_ renaming SubmonoidClass.coe_finsetProd → z8j, Subtype.ext → zkt, Subtype.val → zza, Transcendental → znN, UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors → zJh, UniqueFactorizationMonoid.normalizedFactors → zGM, Valuation → zfZ, Valuation.valuationSubring.integers → z9W, WithZero.le_log_of_exp_le → zeE, WithZero.log → zx3, aFQ.constants → zsm, aaq.Degree → z9p, abG.reduce → zEp, add_assoc → zd8, add_comm → zV6, add_zero → z0a, aeF.toFunction → zLN, ana.center → zZJ, ana.constants → zvZ, associatedPrimes → zMd, baB.Parameters → zG0, charP_of_injective_ringHom → zgG, congrArg → zPw, dN.GeoField → zA7, dN.GeoJets → zlg, faithfulSMul_iff_algebraMap_injective → zSO, finSuccEquivLast → zOE, finrank_top → zl4, isReduced_of_injective → znD, ite_eq_left → zYo, ite_eq_right → zNB, ite_false → zMv, jA.Lower → z0R, jA.translate → zWk, le_antisymm → zWs, le_max_left → zAj, le_max_right → zvf, le_of_not_gt → zHm, le_rfl → zs0, le_sup_left → zPQ, map_add → zrl, map_mul → zok, map_natCast → zGu, map_ne_zero → zyg, map_ne_zero_iff → zw1, map_one → zXs, map_pow → zkq, map_prod → zRa
open _root_ renaming map_sub → zpO, map_sum → zdo, map_zero → zhc, max_eq_left → zWb, max_eq_right → z2J, min_eq_left → zgO, min_eq_right → zmZ, mul_assoc → ztg, mul_comm → zDE, mul_le_of_le_one_left → zZD, mul_ne_zero → zBS, mul_one → zqe, oR.separant → zsz, one_mul → zkF, one_ne_zero → zOR, pow_ne_zero → zm1, pow_succ → zVI, rW.dimension → zIT, right_ne_zero_of_mul → zJ0, ringKrullDim → zqg, smul_eq_mul → zs5, sub_eq_zero → zF3, sub_zero → zTY, zP.Exponent → zHS, zero_add → zOP, zero_le → zJK
set_option autoImplicit true
section
set_option linter.style.haveILetI false
namespace aYZ
noncomputable section
open ac0 NS MvPolynomial
variable {k σ:Type} [zrb k] [zTn σ]
theorem ePm (I:znc (z3y σ k)) (a :σ→k)
    (hred:ahc I (P5 a)) : (projection I a).Finite := by
  classical
  obtain ⟨N,hN⟩:=hred
  let A:=z3y σ k ⧸ I
  let g:=projection I a
  letI:zZE (zM1 k) A:=g.toRingHom.toAlgebra
  change zAa (zM1 k) A
  obtain ⟨s,hs⟩:=(Module.Finite.iff_fg (R:=k)).mp
    (inferInstance :zAa k (z9e I N))
  let T:Submodule (zM1 k) A:=Submodule.span _ (s :Set A)
  have hbase : ∀ x∈z9e I N,x∈T:= by
    intro x hx
    rw [← hs] at hx
    induction hx using zt0 with
    | mem z hz=>exact Submodule.subset_span hz
    | zero=>exact T.zero_mem
    | add x y _ _ hx hy=>exact T.add_mem hx hy
    | smul c x _ hx =>
      have hc: (z1z c:zM1 k)•x=c•x := by
        change g (z1z c)*x=c•x
        rw [← zrD,g.commutes]
        exact (zd5 c x).symm
      rw [← hc]
      exact T.smul_mem _ hx
  have hmul (x :A) : (z7y:zM1 k)•x =
      zVv I (P5 a)*x := by
    change g z7y*x= _
    rw [show g z7y=zVv I (P5 a) from Polynomial.aeval_X _]
  have hall (n:ℕ) : ∀ x∈z9e I n,x∈T:= by
    induction n with
    | zero=>exact fun x hx=>hbase x (quotientDegreeLE_mono I (Nat.zero_le N) hx)
    | succ n ih =>
      intro x hx
      by_cases hn:N≤n
      · obtain ⟨y,hy,z,hz,rfl⟩:=hN n hn x hx
        rw [← hmul]
        exact T.add_mem (ih y hy) (T.smul_mem _ (ih z hz))
      · exact hbase x (zhv I (by omega) hx)
  apply Module.Finite.of_fg_top
  refine ⟨s,top_unique fun x _ => ?_⟩
  obtain ⟨n,hn⟩:=exists_mem_quotientDegreeLE I x
  exact hall n x hn
theorem gDS (I:znc (z3y σ k)) (a :σ→k) (t:k)
  (hred:ahc I (P5 a)) :ahc I (P5 a - C t) := by
 obtain ⟨N,hN⟩:=hred
 refine ⟨N,fun n hn x hx => ?_⟩
 obtain ⟨y,hy,z,hz,rfl⟩:=hN n hn x hx
 refine ⟨y+t•z,(z9e I n).add_mem hy ((z9e I n).smul_mem t hz),
  z,hz,?_⟩
 have ht:t•z=zVv I (C t)*z :=zd5 t z
 rw [ht,zpO]
 ring
private theorem cNm (I:znc (z3y σ k))
   (hI: (zIU I).natDegree=1) :
   ∃ N :ℕ,∀ n≥N,(ztr I (n+1) :ℚ) =
     (ztr I n:ℚ)+affineDegree I:= by
 obtain ⟨N,hN⟩:=zQf I
 refine ⟨N,fun n hn => ?_⟩
 have hD:zHf I=(zIU I).coeff 1 := by
   simp [zHf,z4w,hI]
 rw [hD,← hN (n+1) (by omega),← hN n hn]
 have hP:=Polynomial.eq_X_add_C_of_natDegree_le_one hI.le
 conv_lhs=>rw [hP]
 conv_rhs=>enter [1]; rw [hP]
 simp only [zvF,Polynomial.eval_mul,zFf,Polynomial.eval_X,
   z6H,z4o]
 ring
omit [zTn σ] in
private theorem dVd (I:znc (z3y σ k)) {f :z3y σ k}
    (hf :f.totalDegree≤1) {n:ℕ}
    (hred : ∀ x∈z9e I (n+1),
      ∃ y∈z9e I n,∃ z∈z9e I n,
        x=y+Ideal.Quotient.mk I f*z) :
    z9e I (n+1) =
      z9e I n ⊔ (z9e I n).map (zzN k (zVv I f)) := by
  apply zWs
  · intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩:=hred x hx
    exact Submodule.mem_sup.mpr ⟨y,hy,_,Submodule.mem_map.mpr ⟨z,hz,rfl⟩,rfl⟩
  · apply sup_le (zhv I (Nat.le_succ n))
    rintro x ⟨y,hy,rfl⟩
    simpa only [LinearMap.mulLeft_apply,zg2] using
      zan (ziU hf) hy
private theorem guU (I:znc (z3y σ k))
    (hI:I.IsPrime) (hdeg: (zIU I).natDegree=1)
    {f :z3y σ k} (hf :f.totalDegree≤1) (hred:ahc I f) :
    zq4 (zzN k (zVv I f)) ∧
      ∃ N :ℕ,∀ n≥N,∀ x :z3y σ k ⧸ I,
        zVv I f*x∈z9e I (n+1)→x∈z9e I n:= by
  obtain ⟨N₁,hN₁⟩:=hred
  obtain ⟨N₂,hN₂⟩:=cNm I hdeg
  let N :=max N₁ N₂
  let F:=z9e I
  let H :=ztr I
  let v :=zVv I f
  let m:=zzN k v
  have hstep (n:ℕ) (hn:N≤n) :F (n+1)=F n ⊔ (F n).map m :=
    dVd I hf (hN₁ n ((zAj _ _).trans hn))
  have hv :v≠0:= by
    intro hz
    have he :F (N+1)≤F N := by
      intro x hx
      obtain ⟨y,hy,z,_,he⟩:=hN₁ N (zAj _ _) x hx
      have hxy :x=y := by simpa only [v,hz,z1S,z0a] using he
      exact hxy.symm ▸ hy
    have hd:H (N+1)≤H N :=Submodule.finrank_mono he
    have hle : (H (N+1) :ℚ)≤(H N :ℚ) := by exact_mod_cast hd
    have hg: (H (N+1) :ℚ)=(H N :ℚ)+affineDegree I:=hN₂ N (zvf _ _)
    linarith [affineDegree_pos hI.ne_top]
  letI:I.IsPrime :=hI
  have hm:zq4 m:= fun _ _ h=>mul_left_cancel₀ hv h
  have hdim (n:ℕ) :zsE k ((F n).map m)=H n :=
    (zW6 m hm (F n)).finrank_eq.symm
  have hinter (n:ℕ) (hn:N≤n) :
      (F n).map m=F (n+1) ⊓ (F (n+1)).map m:= by
    have hn' : N₂≤n:=(zvf _ _).trans hn
    have hle : (F n).map m≤F (n+1) ⊓ (F (n+1)).map m:= by
      refine le_inf ?_ (Submodule.map_mono (zhv I (Nat.le_succ n)))
      rw [hstep n hn]
      exact le_sup_right
    have hrank :=Submodule.finrank_sup_add_finrank_inf_eq (F (n+1)) ((F (n+1)).map m)
    rw [← hstep (n+1) (by omega),hdim] at hrank
    change H (n+2)+_=H (n+1)+H (n+1) at hrank
    have hbalance :H (n+2)+H n=H (n+1)+H (n+1) := by
      have h₁: (H (n+1) :ℚ)=(H n:ℚ)+affineDegree I:=hN₂ n hn'
      have h₂: (H (n+2) :ℚ)=(H (n+1) :ℚ)+affineDegree I:=hN₂ (n+1) (by omega)
      exact_mod_cast (show (H (n+2) :ℚ)+(H n:ℚ)=(H (n+1) :ℚ)+(H (n+1) :ℚ) by
        linarith)
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [hdim]
    omega
  refine ⟨hm,N,fun n hn x hx => ?_⟩
  obtain ⟨d,hd⟩:=exists_mem_quotientDegreeLE I x
  induction d with
  | zero=>exact quotientDegreeLE_mono I (Nat.zero_le n) hd
  | succ d ih =>
    by_cases hdn:d<n
    · exact zhv I (by omega) hd
    · have hx' : m x∈F (d+1) ⊓ (F (d+1)).map m :=
        ⟨zhv I (by omega) hx,Submodule.mem_map.mpr ⟨x,hd,rfl⟩⟩
      rw [← hinter d (by omega)] at hx'
      obtain ⟨y,hy,hyx⟩:=Submodule.mem_map.mp hx'
      exact ih ((hm hyx) ▸ hy)
theorem d97 (I:znc (z3y σ k))
    (hI:I.IsPrime) (hdeg: (zIU I).natDegree=1)
    {f :z3y σ k} (hf :f.totalDegree≤1) (hred:ahc I f) :
    (zIU (I ⊔ zye {f})).natDegree=0 ∧
      zHf (I ⊔ zye {f})=zHf I:= by
  let J:=I ⊔ zye {f}
  let F:=z9e I
  let v :=zVv I f
  let q:=z5F k (show I≤J from zPQ)
  obtain ⟨hm,N₁,hN₁⟩:=guU I hI hdeg hf hred
  obtain ⟨N₂,hN₂⟩:=cNm I hdeg
  have hker {x :z3y σ k ⧸ I} (hx :q x=0) :
      ∃ y :z3y σ k ⧸ I,v*y=x := by
    obtain ⟨p,rfl⟩:=zld x
    change zVv J p=0 at hx
    obtain ⟨r,hr,s,hs,he⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    obtain ⟨u,rfl⟩:=Ideal.mem_span_singleton'.mp hs
    refine ⟨zVv I u,?_⟩
    rw [← zok,← he,zrl,Ideal.Quotient.eq_zero_iff_mem.mpr hr,zOP,zDE]
  have hqv :q v=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (zs1 (z5J f))
  have hfun (n:ℕ) (hn:max N₁ N₂≤n) :
      (ztr J (n+1) :ℚ)=zHf I:= by
    let cut:F (n+1) →ₗ[k] z9e J (n+1) :=
      (q.toLinearMap.domRestrict (F (n+1))).codRestrict _ fun x=> by
        obtain ⟨p,hp,he⟩:=mem_quotientDegreeLE.mp x.property
        rw [LinearMap.domRestrict_apply,← he]
        exact ziU hp
    have hcut:zpX cut:= by
      intro y
      obtain ⟨p,hp,he⟩:=mem_quotientDegreeLE.mp y.property
      exact ⟨⟨zVv I p,ziU hp⟩,zkt he⟩
    let mul :F n →ₗ[k] F (n+1) :=
      ((zzN k v).domRestrict (F n)).codRestrict _ fun x=> by
        change v*x.val∈F (n+1)
        simpa only [zg2] using zan (ziU hf) x.property
    have hmul :zq4 mul := fun _ _ h=>zkt (hm (zPw zza h))
    have hkm:z83 cut=zWl mul := by
      ext x
      rw [zeS,LinearMap.mem_range]
      constructor
      · intro hx
        obtain ⟨y,hy⟩:=hker (zPw zza hx)
        have hy' : y∈F n:=hN₁ n ((zAj _ _).trans hn) y (hy.symm ▸ x.property)
        exact ⟨⟨y,hy'⟩,zkt hy⟩
      · rintro ⟨y,rfl⟩
        apply zkt
        change q (v*y.val)=0
        rw [zok,hqv,z1S]
    have hrank :=cut.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hcut,zl4,hkm,LinearMap.finrank_range_of_inj hmul] at hrank
    change ztr J (n+1)+affineHilbertFunction I n =
      ztr I (n+1) at hrank
    have hc: (ztr J (n+1) :ℚ)+(ztr I n:ℚ) =
        (ztr I (n+1) :ℚ) := by exact_mod_cast hrank
    linarith only [hc,hN₂ n ((zvf _ _).trans hn)]
  have hpoly :z1z (zHf I)=zIU J:= by
    apply zpC (N₀:=max N₁ N₂+1)
    intro n hn
    cases n with
    | zero=>omega
    | succ n =>
      rw [zFf]
      exact (hfun n (by omega)).symm
  change (zIU J).natDegree=0∧zHf J=zHf I
  refine ⟨by rw [← hpoly,zti],?_⟩
  change ((zIU J).natDegree.factorial:ℚ) *
    (zIU J).leadingCoeff=zHf I
  rw [← hpoly,zti,Nat.factorial_zero,z4o,zkF,
    Polynomial.leadingCoeff_C]
end
end aYZ
end
section
namespace aYZ
open ac0 YT
theorem proof :ac0.c1 := by
 intro k σ _ _ _ I hI hdim
 obtain ⟨bad,hproper,hbad⟩:=d31 I hdim
 refine ⟨bad,hproper,fun a ha => ?_⟩
 have hred:=bPG (K:=k) I (br3 a) (hbad a ha)
 exact ⟨ePm I a hred,fun t =>
  d97 I hI hdim (bxW a t)
   (gDS I a t hred)⟩
end aYZ
end
section
namespace cyP
theorem proof :aRW.c1 :=
 aRW.dVC aYZ.proof
end cyP
end
section
namespace cxT
noncomputable section
open abG
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {L:Type} [zrb L]
private abbrev a95 (L:Type) [zrb L] :=z3y (Fin 5) L
private theorem a9t {d:ℕ} {s :Set (Fin d)} {i:Fin d} (hi:i∉s)
  (p:z3y (Fin d) L) (hp:z9v i*p∈span (z9v '' s)) :
  p∈span (z9v '' s) := by
 rw [mem_ideal_span_X_image] at hp ⊢
 intro m hm
 have hcoeff :=coeff_X_mul m i p
 have hmem:zhf i 1+m∈(z9v i*p).support :=
  mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
 obtain ⟨j,hj,hne⟩:=hp _ hmem
 have hij:i≠j:= fun e=>hi (e.symm ▸ hj)
 exact ⟨j,hj,by simpa [zSs,zoV,hij] using hne⟩
private theorem eFO {d n:ℕ} (hn:n≤d) :
   zGZ ((zUT (z9v:Fin d→z3y (Fin d) L)).take n) =
     span (z9v '' {j:Fin d | j.val<n}) := by
 rw [← Fin.ofFn_take_eq_take_ofFn hn]
 apply zPw (zye:Set (z3y (Fin d) L)→ znc (z3y (Fin d) L))
 ext p
 change p∈zUT (Fin.take n hn z9v) ↔
   p∈z9v '' {j:Fin d | j.val<n}
 rw [List.mem_ofFn]
 constructor
 · rintro ⟨j,rfl⟩
   exact ⟨Fin.castLE hn j,j.isLt,rfl⟩
 · rintro ⟨j,hj,rfl⟩
   exact ⟨⟨j.val,hj⟩,rfl⟩
private theorem a9u (d:ℕ) :
   IsWeaklyRegular (z3y (Fin d) L)
     (zUT (z9v:Fin d→z3y (Fin d) L)) := by
 classical
 refine ⟨?_⟩
 intro n hn
 have hn' : n<d:= by simpa only [List.length_ofFn] using hn
 rw [zHM,Ideal.mul_top,eFO hn'.le,List.getElem_ofFn]
 let s :Set (Fin d) := {j | j.val<n}
 exact (isSMulRegular_quotient_iff_mem_of_smul_mem
   (span ((z9v:Fin d→z3y (Fin d) L) '' s))
   (z9v ⟨n,hn'⟩)).mpr
   (a9t (s :=s) (i:=⟨n,hn'⟩) (Nat.lt_irrefl n))
private def translation (z :Fin 5→L) :a95 L ≃ₐ[L] a95 L :=
 AlgEquiv.ofAlgHom (zIe (fun i=>z9v i - C (z i))) (zIe (fun i=>z9v i+C (z i)))
  (zpH (fun i=> by simp))
  (zpH (fun i=> by simp))
private def aX6 (L:Type) [zrb L] :a95 L ≃ₐ[L] Total L :=
 (zGY L (_root_.finSuccEquiv 4)).trans (optionEquivRight L (Fin 4))
private theorem gCs :aX6 L (z9v 0)=C Polynomial.X:= by
 rw [aX6,zfq,zyk,rename_X,
  _root_.finSuccEquiv_zero,optionEquivRight_X_none]
private theorem gCr (i:Fin 4) :aX6 L (z9v i.succ)=z9v i:= by
 rw [aX6,zfq,zyk,rename_X,
  _root_.finSuccEquiv_succ,optionEquivRight_X_some]
private theorem gCq (c:L) :aX6 L (C c)=C (z1z c) := by
 rw [aX6,zfq,zyk,rename_C,optionEquivRight_C]
private theorem buP (y :Fin 4→L) :
   ∃ rs :List (aud y),rs.length=5 ∧
     (∀ a∈rs,a∈zrY (aud y))∧IsRegular (aud y) rs := by
 let z :Fin 5→L:=Fin.cases 0 y
 let e :=((translation z).trans (aX6 L)).toRingEquiv
 let rs :=zUT (z9v:Fin 5→a95 L)
 have hcongr :List.Forall₂ (fun (r :a95 L) (s :Total L) =>
     ∀ x :a95 L,e (r•x)=s•e x) rs (rs.map e) :=
   List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x=>e.map_mul r x)
 have hwr :IsWeaklyRegular (Total L) (rs.map e) :=
   (e.toAddEquiv.isWeaklyRegular_congr hcongr).mp (a9u 5)
 have hm (p:Total L) (hp:p∈rs.map e) :p∈aJS y := by
   obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hp
   obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hw
   change zEp (aX6 L (zIe (fun j=>z9v j - C (z j)) (z9v i)))∈wN y
   rw [mem_vanishingIdeal_singleton_iff,zTw,zpO]
   refine Fin.cases ?_ (fun j => ?_) i <;>
     simp [z,zEp,gCs,gCr,gCq]
 refine ⟨(rs.map e).map (algebraMap (Total L) (aud y)),by simp [rs],?_,
   hwr.isRegular_of_isLocalization_of_mem (aud y) (aJS y) hm⟩
 intro x hx
 obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hx
 exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (aud y) (aJS y) w).mpr (hm w hw)
private theorem gCz (g:Fin 4→Total L) (y :Fin 4→L)
   (hy :wN y∈(H8 fun i=>zEp (g i)).minimalPrimes) :
   aJS y∈(H8 g ⊔ span {C z7y}).minimalPrimes := by
 have hsurj:zpX (zEp (L:=L)) := by
   apply MvPolynomial.map_surjective
   intro a
   exact ⟨z1z a,zFf⟩
 have hmap : (H8 g).map zEp=H8 (fun i=>zEp (g i)) := by
   rw [H8,zlN,← Set.range_comp']
   rfl
 have hker :zdq (zEp (L:=L))=span {C z7y} := by
   rw [zEp,MvPolynomial.ker_map,Polynomial.ker_evalRingHom,Polynomial.C_0,zTY,
     zlN,zyl]
 have h:=Ideal.minimalPrimes_comap_of_surjective hsurj (hmap ▸ hy)
 rwa [Ideal.comap_map_of_surjective _ hsurj,← RingHom.ker_eq_comap_bot,hker] at h
theorem proof :abG.c2 := by
 classical
 intro L _ _ g y hy
 let R:=aud y
 let a :=z12 (Total L) R
 let _:zZE L R:=(a.comp (z12 L (Total L))).toAlgebra
 let front:=zUT fun i=>a (g i)
 let t:=a (C z7y)
 have hfront:zGZ front=(H8 g).map a := by
   rw [H8,zlN,← Set.range_comp']
   exact zPw span (Set.ext (List.mem_ofFn' (fun i=>a (g i))))
 have hrad: (zGZ (front ++ [t])).radical=zrY R:= by
   rw [Ideal.ofList_append,Ideal.ofList_singleton,hfront,show span {t} =
     (span {C z7y}).map a by rw [zlN,zyl]]
   rw [← Ideal.map_sup,z8P
     R (aJS y) _ (gCz g y hy),IsLocalization.AtPrime.map_eq_maximalIdeal]
 obtain ⟨rs,hlen,hmem,hreg⟩:=buP y
 have hparams :=bjD.bPS (k :=L) rs (front ++ [t])
   (by simpa [front] using hlen) hmem hreg hrad
 have hlast :=((isWeaklyRegular_append_iff R front [t]).mp hparams).2
 have hc:=(isWeaklyRegular_singleton_iff _ _).mp hlast
 rw [zHM,Ideal.mul_top,hfront] at hc
 exact hc
end
end cxT
end
section
namespace baj
noncomputable section
open aR Rj MvPolynomial
abbrev alQ:Fin 3→ℕ:= fun _=>1
abbrev aIL:Fin 3→ℕ := ![1,0,1]
abbrev aJM:Fin 3→ℕ := ![2,0,1]
theorem aT5 (e :adf) :e.weight alQ=e 0+e 1+e 2 := by
 simp [z1K,zCj,zs5,zd8]
theorem eHN (e :adf) :e.weight aIL=e 0+e 2 := by
 simp [z1K,zCj,zs5]
theorem bxy (e :adf) :e.weight aJM=2*e 0+e 2 := by
 simp [z1K,zCj,zs5,z5A]
abbrev bza (d:ℕ) := ↥{e :adf | e.weight alQ=d}
abbrev a9V (d:ℕ) :=zQW ao {e :adf | e.weight alQ=d}
abbrev a9I (d:ℕ) (F:Flag) :=
 {e :bza d //
   (e.val.weight aIL:ℤ)<F.iy ∨
   (e.val.weight aJM:ℤ)<F.HE}
private abbrev Triangle (n:ℕ) :=Σ s :Fin n,Fin (s.val+1)
private theorem cuc (n:ℕ) : (zhP (Triangle n) :ℤ)=sG n:= by
 have hs : (∑ s :Fin n,(s.val+1))=(n+1).choose 2 := by
   rw [Fin.sum_univ_eq_sum_range (fun i:ℕ=>i+1) n]
   induction n with
   | zero=>simp
   | succ n ih =>
     rw [zpB,ih]
     simp [Nat.choose_succ_succ,zk3]
     omega
 rw [zTU]
 simp only [Fintype.card_fin,hs,zzd,z2h,
   Int.natCast_div,z2R,z6H,z4o,sG,zDE]
 rfl
private def cJL (d:ℕ) :bza d ≃ Triangle (d+1) where
 toFun e :=⟨⟨e.val 0+e.val 2,by
  have h:=e.property
  simp only [zsi,aT5] at h
  omega⟩,⟨e.val 0,by
    change e.val 0<e.val 0+e.val 2+1
    omega⟩⟩
 invFun s :=⟨Finsupp.equivFunOnFinite.symm ![s.2.val,d - s.1.val,s.1.val - s.2.val],by
  have h:=s.1.isLt
  have h' := s.2.isLt
  simp only [zsi,aT5]
  change s.2.val+(d - s.1.val)+(s.1.val - s.2.val)=d
  omega⟩
 left_inv e := by
  have h:=e.property
  simp only [zsi,aT5] at h
  apply zkt
  ext i:1
  fin_cases i
  · rfl
  · change d-(e.val 0+e.val 2)=e.val 1
    omega
  · change e.val 0+e.val 2 - e.val 0=e.val 2
    omega
 right_inv s := by
  have h:=s.2.isLt
  have ht:s.2.val+(s.1.val - s.2.val)=s.1.val := by omega
  exact Sigma.ext (Fin.ext ht) ((Fin.heq_ext_iff (zPw (· + 1) ht)).mpr rfl)
noncomputable instance gPK (d:ℕ) :
  z85 (bza d) :=
 Fintype.ofEquiv (Triangle (d+1)) (cJL d).symm
noncomputable instance gOY (d:ℕ) (F:Flag) :z85 (a9I d F) :=
 @Fintype.ofFinite _ (Finite.of_injective zza Subtype.val_injective)
instance gPL (d:ℕ) :zAa ao (a9V d) :=
 Module.Finite.of_basis (zzc ao {e :adf | e.weight alQ=d})
theorem dVl (d:ℕ) :
  (zsE ao (a9V d) :ℤ)=sG ((d:ℤ)+1) := by
 rw [Module.finrank_eq_card_basis (zzc ao
  {e :adf | e.weight alQ=d})]
 change (zhP (bza d) :ℤ)= _
 rw [Fintype.card_congr (cJL d)]
 simpa using cuc (d+1)
private def ahX (F:Flag) :ℤ:=max 0 (max F.iy ((F.HE+1)/2))
private def Uy (F:Flag) :ℤ:=max (ahX F) F.HE
private def bU4 (d:ℕ) (F:Flag) (e :a9I d F) :
    Triangle (ahX F).toNat ⊕ Triangle (Uy F-ahX F).toNat :=
  if h: (e.val.val 0+e.val.val 2 :ℕ)<(ahX F).toNat then
    .inl ⟨⟨e.val.val 0+e.val.val 2,h⟩,⟨e.val.val 0,by
      change e.val.val 0<e.val.val 0+e.val.val 2+1
      omega⟩⟩
  else
    .inr ⟨⟨e.val.val 0+e.val.val 2 - (ahX F).toNat+e.val.val 0,by
      have hu:0≤ahX F:=zAj _ _
      have ho:F.iy≤ahX F:=(zAj _ _).trans (zvf _ _)
      have hw:F.HE≤Uy F:=zvf _ _
      have he :=e.property
      rw [eHN,bxy] at he
      omega⟩,⟨e.val.val 0,by
        change e.val.val 0 <
          e.val.val 0+e.val.val 2 - (ahX F).toNat+e.val.val 0+1
        omega⟩⟩
private theorem dxX (d:ℕ) (F:Flag) :
    zq4 (bU4 d F) := by
  intro e f h
  have hd:=e.val.property
  have hd' := f.val.property
  simp only [zsi,aT5] at hd hd'
  let coords :Triangle (ahX F).toNat ⊕ Triangle (Uy F-ahX F).toNat →
      ℕ×ℕ:=Sum.elim (fun s=>(s.1.val,s.2.val))
        (fun s=>(s.1.val - s.2.val+(ahX F).toNat,s.2.val))
  have project (a :a9I d F) :
      coords (bU4 d F a)=(a.val.val 0+a.val.val 2,a.val.val 0) := by
    unfold bU4
    split
    · rfl
    · change (a.val.val 0+a.val.val 2 - (ahX F).toNat+a.val.val 0 -
        a.val.val 0+(ahX F).toNat,a.val.val 0)= _
      rw [z2h,Nat.sub_add_cancel (by omega)]
  have hc:=zPw coords h
  rw [project,project] at hc
  obtain ⟨ht,hb⟩:=Prod.mk.inj hc
  apply zkt
  apply zkt
  ext i:1
  fin_cases i
  · exact hb
  · change e.val.val 1=f.val.val 1
    omega
  · change e.val.val 2=f.val.val 2
    omega
theorem dxY (d:ℕ) (F:Flag) : (zhP (a9I d F) :ℤ)≤yC F:= by
  have h:=Fintype.card_le_of_injective _ (dxX d F)
  have hu:0≤ahX F:=zAj _ _
  have hv :ahX F≤Uy F:=zAj _ _
  have hz :0≤Uy F-ahX F:=sub_nonneg.mpr hv
  have hcast: (zhP (a9I d F) :ℤ) ≤
      (zhP (Triangle (ahX F).toNat ⊕
        Triangle (Uy F-ahX F).toNat) :ℤ) := by exact_mod_cast h
  rwa [Fintype.card_sum,z6H,cuc,cuc,zi4 hu,
    zi4 hz] at hcast
end
end baj
end
section
namespace baj
noncomputable section
open aR Rj MvPolynomial
local notation "V" => (MvPolynomial.X:Fin 3→lK)
def aTy :Fin 3→Fin 3→lK :=
 ![![V 1,V 2,V 0],![V 0,V 2,V 1],acw]
def bY (i:Fin 3) :lK →ₐ[ao] lK:=bind₁ (aTy i)
theorem aYd (j:Fin 3) : (V j).IsWeightedHomogeneous alQ 1 :=
 isWeightedHomogeneous_X ao alQ j
private theorem dIC (i:Fin 3) {d:ℕ} {f :lK}
  (hf :f.IsWeightedHomogeneous alQ d) :
  (bY i f).IsWeightedHomogeneous alQ d:= by
 apply hf.bind₁
 intro j
 fin_cases i <;> fin_cases j <;>
  simp [aTy,acw,aYd]
 exact ((aYd 0).add (aYd 1)).sub (aYd 2)
def bAa (F:Fin 3→Flag) (f :lK) :Prop :=
  ∀ i:Fin 3,
    bY i f∈zlK aIL (F i).iy.toNat ∧
    bY i f∈zlK aJM (F i).HE.toNat
private abbrev bQY (d:ℕ) (F:Fin 3→Flag) :=Σ i:Fin 3,a9I d (F i)
def bqh (d:ℕ) (F:Fin 3→Flag) :a9V d →ₗ[ao] (bQY d F→ao) :=
  LinearMap.pi fun t =>
    ((lcoeff ao t.2.val.val).comp (bY t.1).toLinearMap).domRestrict (a9V d)
theorem cJ1 {d:ℕ} (f :a9V d) :
  (f :lK).IsWeightedHomogeneous alQ d:= by
 intro e he
 exact (mem_restrictSupport_iff ao).mp f.property (mem_support_iff.mpr he)
theorem ezV {d:ℕ} {F:Fin 3→Flag} (f :z83 (bqh d F)) :
    bAa F (f.val :lK) := by
  intro i
  have ok (e :adf) (he :e∈(bY i (f.val :lK)).support) :
      ¬ ((e.weight aIL:ℤ)<(F i).iy ∨
        (e.weight aJM:ℤ)<(F i).HE) := by
    intro hbad
    have hne :=mem_support_iff.mp he
    have hd:=dIC i (cJ1 f.val) hne
    exact hne (congrFun (LinearMap.mem_ker.mp f.property) ⟨i,⟨⟨e,hd⟩,hbad⟩⟩)
  constructor
  · apply mem_restrictWeightedOrder.mpr
    intro e he
    have h:=not_or.mp (ok e he)
    omega
  · apply mem_restrictWeightedOrder.mpr
    intro e he
    have h:=not_or.mp (ok e he)
    omega
theorem ec2 (d:ℕ) (F:Fin 3→Flag) :
   sG ((d:ℤ)+1) - ∑ i,yC (F i) ≤
     (zsE ao (z83 (bqh d F)) :ℤ) := by
 let L:=bqh d F
 have hd:=L.finrank_range_add_finrank_ker
 have hr : (zsE ao (zWl L) :ℤ) ≤
     zhP (bQY d F) := by
   have h:=Submodule.finrank_le (zWl L)
   rw [Module.finrank_pi] at h
   exact_mod_cast h
 have hc: (zhP (bQY d F) :ℤ) ≤ ∑ i,yC (F i) := by
   rw [zTU,zCt]
   exact zQk fun i _=>dxY d (F i)
 rw [← dVl d]
 change _≤(zsE ao (z83 L) :ℤ)
 omega
private def b6v :Fin 3→lK := ![V 2,V 0,V 1]
private theorem gGU (f :lK) :bind₁ b6v (bY 0 f)=f := by
 rw [bY,bind₁_bind₁]
 have him: (fun i=>bind₁ b6v (aTy 0 i))=V:= by
  funext i
  fin_cases i <;> simp [b6v,aTy]
 rw [him,bind₁_X_left]
 rfl
private theorem diD (f :lK) :bY 1 (bY 1 f)=f := by
 simp only [bY,bind₁_bind₁]
 have him: (fun i=>bind₁ (aTy 1) (aTy 1 i))=V:= by
  funext i
  fin_cases i <;> simp [aTy]
 rw [him,bind₁_X_left]
 rfl
private abbrev eQh:Fin 3→ℕ := ![1,1,0]
private abbrev eQi:Fin 3→ℕ := ![2,1,0]
theorem eIi {q:ℕ} {g:ℤ} {f :lK}
  (hd:f.IsWeightedHomogeneous alQ (iO q))
  (hf :bAa (pT q g) f) :
  ∃ hsrc :f∈aqz q g,(⟨f,hsrc⟩:aqz q g) ∈
    z83 (aPi q g) := by
 have hP:f∈zlK zf5 (-g).toNat := by
  rw [← gGU f]
  apply zku _ (hf 0).2
  intro i
  fin_cases i <;> apply z9j <;> decide
 have hQo:f∈zlK eQh ((iO q:ℤ) - 1150).toNat := by
  rw [← diD f]
  apply zku _ (hf 1).1
  intro i
  fin_cases i <;> apply z9j <;> decide
 have hQw:f∈zlK eQi (2*(iO q:ℤ) - 2300).toNat := by
  rw [← diD f]
  apply zku _ (hf 1).2
  intro i
  fin_cases i <;> apply z9j <;> decide
 have hsrc :f∈aqz q g:= by
  apply (mem_restrictSupport_iff ao).mpr
  intro e he
  have hdeg:=hd (mem_support_iff.mp he)
  have hn:=mem_restrictWeightedOrder.mp hP e he
  have ho:=mem_restrictWeightedOrder.mp hQo e he
  have hw:=mem_restrictWeightedOrder.mp hQw e he
  change e.weight alQ=iO q ∧ -g≤(e.weight zf5 :ℤ) ∧
    e.weight zf5≤2300∧e 2≤1150
  rw [aT5] at hdeg
  simp [z1K,zCj,zs5,z5A] at hn ho hw ⊢
  omega
 refine ⟨hsrc,LinearMap.mem_ker.mpr ?_⟩
 apply (weightedTruncation_eq_zero_iff _ _ _).mpr
 exact (hf 2).2
end
end baj
end
section
namespace baj
noncomputable section
open aR Rj MvPolynomial
open scoped BigOperators
local notation "V" => (MvPolynomial.X:Fin 3→lK)
private def factor :Fin 6→lK :=
 let x :=V 0-V 1
 let y :=V 1
 let z :=V 2
 ![z,y,x,x+y,x+z,x*y + x*z+y*z]
private def product (p:kJ) :lK := ∏ j,factor j^p j
private theorem b2K (j:Fin 6) :factor j≠0:= by
 let point :Fin 6→Fin 3→ao :=
  ![![0,0,1],![0,1,0],![1,0,0],![1,0,0],![1,0,0],![1,1,1]]
 intro h
 have he :=zPw (fun f :lK=>eval (point j) f) h
 fin_cases j <;> simp [point,factor] at he
private theorem d5V (j:Fin 6) :
   (factor j).IsWeightedHomogeneous alQ (yE j).toNat := by
 have hx :=(aYd 0).sub (aYd 1)
 have hy :=aYd 1
 have hz :=aYd 2
 fin_cases j
 · exact hz
 · exact hy
 · exact hx
 · exact hx.add hy
 · exact hx.add hz
 · exact ((hx.mul hy).add (hx.mul hz)).add (hy.mul hz)
private def bWS (i:Fin 3) (j:Fin 6) :lK :=
 let a :=V 0
 let b:=V 1
 let c:=V 2
 (![![a,c,b - c,b,b - c+a,b*c - c*c+b*a],
   ![b,c,a - c,a,a - c+b,a*c - c*c+a*b],
   ![c,b,a - c,a - c+b,a,a*b - c*c+a*c]] :Fin 3→Fin 6→lK) i j
private theorem bCz (i:Fin 3) (j:Fin 6) :
  bY i (factor j)=bWS i j:= by
 fin_cases i <;> fin_cases j <;> simp [bY,aTy,acw,factor,bWS] <;> ring
private def aw4 (f :lK) (a b:ℕ) :Prop :=
 f∈zlK aIL a∧f∈zlK aJM b
private theorem a6i (f :lK) :aw4 f 0 0:= by simp [aw4]
private theorem caD (i:Fin 3) (a b:ℕ) (ha :a≤aIL i)
   (hb:b≤aJM i) :aw4 (V i) a b :=
 ⟨z9j _ i ha,z9j _ i hb⟩
private theorem bfZ (i j:Fin 3) (a b:ℕ) (ha :a≤aIL i+aIL j)
    (hb:b≤aJM i+aJM j) :aw4 (V i*V j) a b :=
  ⟨z2F _ ha
      (zgN (z9j _ i zs0)
        (z9j _ j zs0)),
    z2F _ hb
      (zgN (z9j _ i zs0)
        (z9j _ j zs0))⟩
private theorem bJX {f g:lK} {a b:ℕ}
   (hf :aw4 f a b) (hg:aw4 g a b) :aw4 (f - g) a b :=
 ⟨zMG _ hf.1 hg.1,zMG _ hf.2 hg.2⟩
private theorem caC {f g h:lK} {a b:ℕ}
   (hf :aw4 f a b) (hg:aw4 g a b) (hh:aw4 h a b) :
   aw4 (f - g+h) a b :=
 ⟨zcy _ (bJX hf hg).1 hh.1,
   zcy _ (bJX hf hg).2 hh.2⟩
private theorem cN8 (j:Fin 6) (i:Fin 3) :
   bY i (factor j)∈zlK aIL (Jd j i).iy.toNat ∧
   bY i (factor j)∈zlK aJM (Jd j i).HE.toNat := by
 rw [bCz]
 change aw4 (bWS i j) (Jd j i).iy.toNat (Jd j i).HE.toNat
 have a₁₁:=caD 0 1 1 (by decide) (by decide)
 have a₁₂:=caD 0 1 2 (by decide) (by decide)
 have c₁₁:=caD 2 1 1 (by decide) (by decide)
 have ac:=bfZ 0 2 1 2 (by decide) (by decide)
 have ab:=bfZ 0 1 1 2 (by decide) (by decide)
 have cc:=bfZ 2 2 1 2 (by decide) (by decide)
 fin_cases i <;> fin_cases j
 · exact a₁₂
 · exact c₁₁
 · exact a6i _
 · exact a6i _
 · exact a6i _
 · exact caC (bfZ 1 2 1 1 (by decide) (by decide))
     (bfZ 2 2 1 1 (by decide) (by decide)) (bfZ 1 0 1 1 (by decide) (by decide))
 · exact a6i _
 · exact c₁₁
 · exact bJX a₁₁ c₁₁
 · exact a₁₂
 · exact a6i _
 · exact caC ac cc ab
 · exact c₁₁
 · exact a6i _
 · exact bJX a₁₁ c₁₁
 · exact a6i _
 · exact a₁₂
 · exact caC ab cc ac
private theorem cEp (p:kJ) (v :Fin 6→ℤ) (hv : ∀ j,0≤v j) :
  ((∑ j,p j*(v j).toNat :ℕ) :ℤ) = ∑ j,(p j:ℤ)*v j:= by
 simp [zCt,hv]
private theorem eO0 (q:ℕ) (p:kJ) {f :lK}
   (hn:0≤K6 q p)
   (hf :f.IsWeightedHomogeneous alQ (K6 q p).toNat) :
   (product p*f).IsWeightedHomogeneous alQ (iO q) := by
 have hp: (product p).IsWeightedHomogeneous alQ (∑ j,p j*(yE j).toNat) := by
   apply IsWeightedHomogeneous.prod
   intro j _
   simpa only [Nat.nsmul_eq_mul] using (d5V j).pow (p j)
 have hc:=cEp p yE (by intro j; unfold yE; split <;> decide)
 have hsum: (∑ j,p j*(yE j).toNat)+(K6 q p).toNat =
     iO q:= by
   unfold K6 at hn ⊢
   omega
 rw [← hsum]
 exact hp.mul hf
private theorem aIu (p:kJ) (i:Fin 3) (w:Fin 3→ℕ) (a :ℤ) (v :Fin 6→ℤ)
  (hv : ∀ j,0≤v j)
  (hfactor : ∀ j,bY i (factor j)∈zlK w (v j).toNat)
  {f :lK}
  (hf :bY i f∈zlK w (a - ∑ j,(p j:ℤ)*v j).toNat) :
  bY i (product p*f)∈zlK w a.toNat := by
 have hp:bY i (product p)∈zlK w (∑ j,p j*(v j).toNat) := by
  simp only [product,zRa,zkq]
  exact prod_mem_restrictWeightedOrder _ fun j _=>pow_mem_restrictWeightedOrder (hfactor j) (p j)
 rw [zok]
 refine z2F w ?_ (zgN hp hf)
 have hc:=cEp p v hv
 omega
private theorem eO1 (q:ℕ) (g:ℤ) (p:kJ) {f :lK}
  (hf :bAa (D8 q g p) f) :bAa (pT q g) (product p*f) := by
 intro i
 exact ⟨aIu p i aIL (pT q g i).iy
    (fun j=>(Jd j i).iy)
    (by intro j; fin_cases j <;> fin_cases i <;> decide)
    (fun j=>(cN8 j i).1) (hf i).1,
  aIu p i aJM (pT q g i).HE
    (fun j=>(Jd j i).HE)
    (by intro j; fin_cases j <;> fin_cases i <;> decide)
    (fun j=>(cN8 j i).2) (hf i).2⟩
private theorem ewc (q:ℕ) (g:ℤ) (p:kJ) (hn:0≤K6 q p) :
   zsE ao (z83 (bqh (K6 q p).toNat (D8 q g p))) ≤
     zsE ao (z83 (aPi q g)) := by
 let S:=z83 (bqh (K6 q p).toNat (D8 q g p))
 have h (f :S) :=eIi (q:=q) (g:=g)
   (eO0 q p hn (cJ1 f.val))
   (eO1 q g p (ezV f))
 let L:S →ₗ[ao] lK :=
   (zzN ao (product p)).comp
     (((a9V (K6 q p).toNat).subtype).comp S.subtype)
 let M:=L.codRestrict (aqz q g) (fun f=>(h f).choose)
 let N :=M.codRestrict (z83 (aPi q g)) (fun f=>(h f).choose_spec)
 apply zdv (f :=N)
 intro f f' hff'
 apply zkt
 apply zkt
 have hp:product p≠0 :=
   Finset.prod_ne_zero_iff.mpr fun j _=>zm1 _ (b2K j)
 exact mul_left_cancel₀ hp (zPw (fun a=>(a.val :lK)) hff')
theorem proof :Rj.c2 := by
 intro q _ k _ p
 let d:=K6 q p
 by_cases hn:K6 q p<0
 · simp [m5,hn]
 have hnonneg:0≤d:=zHm hn
 have hres :=ec2 d.toNat (D8 q (zve k) p)
 rw [zi4 hnonneg] at hres
 have hl:=ewc q (zve k) p hnonneg
 simp only [m5,hn,zMv]
 exact hres.trans (by exact_mod_cast hl)
end
end baj
end
section
namespace bzP
noncomputable section
open zP aaq aA9 MvPolynomial
open scoped Pointwise
variable {A:Fin 4→zJe zHS}
abbrev Ambient (A:Fin 4→zJe zHS) :=z3y (Fin 4) (af A)
abbrev stamp (d:z9p) :Exponent:=Finsupp.equivFunOnFinite.symm d
theorem dft (d:z9p) (i:Fin 4) :
  stamp (shift d i 1)=stamp d+Finsupp.single i 1 := by
 ext j
 simp [shift,zSs,zsZ]
theorem aC6 (d e :z9p) :
  Bc A (d+e)=Bc A d+Bc A e := by
 simp only [Bc,Pi.add_apply,add_nsmul,zfW]
theorem aUt (i:Fin 4) :Bc A (Pi.single i 1)=A i:= by
 classical
 unfold Bc
 rw [zi6 i]
 · simp
 · intro j _ hj
   rw [Pi.single_eq_of_ne hj,zero_nsmul]
 · simp
private theorem bJu {d:z9p} {e :zHS} (he :e∈Bc A d)
  (c:fZ A) :ztt e c∈dO A d:= by
 have h:ztt e (1 :fZ A)∈dO A d :=
  zBO ⟨⟨e,he⟩,rfl⟩
 simpa only [smul_monomial,zs5,zqe] using (dO A d).smul_mem c h
private theorem eEc {d e :z9p} {p q:af A}
   (hp:p∈dO A d) (hq:q∈dO A e) :p*q∈dO A (d+e) := by
 induction hp using zt0 with
 | mem p hp =>
   obtain ⟨a,rfl⟩:=hp
   induction hq using zt0 with
   | mem q hq =>
     obtain ⟨b,rfl⟩:=hq
     rw [zDU]
     apply bJu
     rw [aC6]
     exact Set.mem_add.mpr ⟨a,a.2,b,b.2,rfl⟩
   | zero=>simp
   | add q r _ _ hq hr=>simpa only [mul_add] using (dO A _).add_mem hq hr
   | smul c q _ hq=>simpa only [mul_smul_comm] using (dO A _).smul_mem c hq
 | zero=>simp
 | add p r _ _ hp hr=>simpa only [add_mul] using (dO A _).add_mem hp hr
 | smul c p _ hp=>simpa only [smul_mul_assoc] using (dO A _).smul_mem c hp
def generator (t:Σ i:Fin 4,↥(A i)) :Ambient A :=
 ztt (zhf t.1 1) (ztt t.2.val 1)
def model (A:Fin 4→zJe zHS) :Subalgebra (fZ A) (Ambient A) :=
 Algebra.adjoin _ (Set.range (generator (A:=A)))
instance gQB:za6 (model A) :=
 Subalgebra.toCommRing (R:=fZ A) (A:=Ambient A) (model A)
instance :IsNoetherianRing (model A) := by
 classical
 let:zUK (fZ A) (model A) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range generator)
 exact Algebra.FiniteType.isNoetherianRing (fZ A) (model A)
def gen (i:Fin 4) (a : ↥(A i)) :model A :=
 ⟨generator ⟨i,a⟩,Algebra.subset_adjoin ⟨⟨i,a⟩,rfl⟩⟩
def bY (a :Chart A) :model A := ∏ i,gen i (a i)
private theorem b9n {ι:Type*} (s :zJe ι) (d e :ι→zHS) :
   (ztt (∑ x∈s,d x) (ztt (∑ x∈s,e x) 1) :Ambient A) =
     ∏ x∈s,ztt (d x) (ztt (e x) 1) := by
 rw [monomial_sum_one,monomial_sum_prod]
private theorem sum_single (d:z9p) : (∑ i,zhf i (d i))=stamp d:= by
 classical
 ext j
 simp [Finset.sum_apply',zoV]
theorem dIO (a :Chart A) (m:ℕ) :
   ((bY a^m:model A) :Ambient A)=ztt (stamp (fun _=>m)) (a2m a m) := by
 have h: ((bY a :model A) :Ambient A) =
     ztt (stamp (fun _=>1)) (ztt (∑ i,(a i).val) 1) := by
   rw [← sum_single,b9n]
   exact z8j _ _
 rw [Subalgebra.coe_pow,h,zpV,zpV,one_pow,a2m]
 congr
 ext i
 simp
private theorem factors {d:z9p} {e :zHS} (he :e∈Bc A d) :
  ∃ f : ∀ i,Fin (d i) → ↥(A i),∑ i,∑ x,(f i x).val=e := by
 classical
 obtain ⟨u,hu,rfl⟩:=(Set.mem_fintype_sum _ _).mp he
 have hf (i:Fin 4) : ∃ f :Fin (d i) → ↥(A i),∑ x,(f x).val=u i:= by
  obtain ⟨v,hv,heq⟩:=Set.mem_nsmul_iff_sum.mp (hu i)
  exact ⟨fun x=>⟨v x,hv x⟩,heq⟩
 choose f hf using hf
 exact ⟨f,zUo rfl fun i _=>hf i⟩
private theorem cOd {d:z9p} (f : ∀ i,Fin (d i) → ↥(A i)) :
   ((∏ i,∏ x,gen i (f i x) :model A) :Ambient A) =
     ztt (stamp d) (ztt (∑ i,∑ x,(f i x).val) 1) := by
 classical
 rw [← sum_single,b9n,z8j]
 apply zX3 rfl
 intro i _
 rw [z8j]
 have h: (∑ _:Fin (d i),zhf i (1 :ℕ))=zhf i (d i) := by
   ext j
   simp [zoV]
 rw [← h,b9n]
 rfl
private theorem eDW {d e :zHS} (he :e∈Bc A d) :
  ztt d (ztt e 1)∈model A:= by
 obtain ⟨f,hf⟩:=factors he
 have hp:=(∏ i,∏ x,gen i (f i x)).property
 rw [cOd,hf] at hp
 simpa only [stamp,zWu] using hp
def tag (d:zHS) {p:af A} (hp:p∈dO A d) :model A:= by
 refine ⟨ztt d p,?_⟩
 induction hp using zt0 with
 | mem p hp=>obtain ⟨e,rfl⟩:=hp; exact eDW e.2
 | zero=>rw [map_zero]; exact (model A).zero_mem
 | add p q _ _ hp hq=>simpa only [map_add] using (model A).add_mem hp hq
 | smul c p _ hp=>simpa only [smul_monomial] using (model A).smul_mem hp c
private def eK8 (A:Fin 4→zJe zHS) :
  Subalgebra (fZ A) (Ambient A) where
 carrier := {p | ∀ d:zHS,p.coeff d∈dO A d}
 zero_mem' := by simp
 one_mem' := by
  intro d
  by_cases h:d=0
  · subst d
    simpa [Bc] using (bJu (A:=A) (d:=0) (e :=0) (by simp [Bc]) 1)
  · simp [coeff_one,z9m h]
 add_mem' := by
  intro p q hp hq d
  exact (dO A d).add_mem (hp d) (hq d)
 mul_mem' := by
  classical
  intro p q hp hq d
  rw [zcz]
  refine zo3 _ fun e he => ?_
  have h:=Finset.HasAntidiagonal.mem_antidiagonal.mp he
  exact h ▸ eEc (hp e.1) (hq e.2)
 algebraMap_mem' := by
  intro c d
  rw [zYY (fZ A) (af A) (Ambient A)]
  change (C (C c) :Ambient A).coeff d∈dO A d
  by_cases h:d=0
  · subst d
    rw [coeff_zero_C]
    exact bJu (A:=A) (d:=0) (e :=0) (by simp [Bc]) c
  · simp [coeff_C,z9m h]
theorem bXQ (f :model A) (d:zHS) : (f :Ambient A).coeff d∈dO A d:= by
 have h:model A≤eK8 A:= by
  apply Algebra.adjoin_le
  rintro _ ⟨⟨i,a⟩,rfl⟩ d
  by_cases hd:d=zhf i 1
  · subst d
    simp only [generator,z0I]
    apply bJu
    rw [zsZ,aUt]
    exact Finset.mem_coe.mpr a.2
  · simp [generator,z0I,z9m hd]
 exact (h f.property : ∀ d:zHS,(f :Ambient A).coeff d∈dO A d) d
def proj (d:zHS) (f :model A) :model A:=tag d (bXQ f d)
def Jy (A:Fin 4→zJe zHS) (m:ℕ) :znc (model A) :=
 zye (Set.range fun a :Chart A=>bY a^m)
private theorem d55 (hz : ∀ i,0∈A i) {d:z9p} {m:ℕ}
    (hd : ∀ i,(A i).card*m≤d i) (f : ∀ i,Fin (d i) → ↥(A i)) :
    ∃ a :Chart A,bY a^m ∣ ∏ i,∏ x,gen i (f i x) := by
  classical
  have h (i:Fin 4) : ∃ a : ↥(A i),(gen i a)^m ∣ ∏ x,gen i (f i x) := by
    let:Nonempty ↥(A i) :=⟨⟨0,hz i⟩⟩
    obtain ⟨a,_,ha⟩:=Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s :=zdB) (t:=zdB) (f :=f i) (n:=m)
      (fun _ _=>zTc _) Finset.univ_nonempty (by simpa using hd i)
    obtain ⟨s,hs,hsCard⟩:=Finset.exists_subset_card_eq ha
    refine ⟨a,∏ x∈zdB \ s,gen i (f i x),?_⟩
    have he : (∏ x∈s,gen i (f i x))=gen i a^m:= by
      calc
        _ = ∏ _x∈s,gen i a :=
          zX3 rfl fun x hx=>zPw (gen i) (Finset.mem_filter.mp (hs hx)).2
        _ = _:= by rw [Finset.prod_const,hsCard]
    rw [← he,zDE,Finset.prod_sdiff (Finset.subset_univ s)]
  choose a ha using h
  refine ⟨a,?_⟩
  unfold bY
  rw [← Finset.prod_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _=>ha i
theorem gyT (hz : ∀ i,0∈A i) {d:zHS} {m:ℕ}
   (hd : ∀ i,(A i).card*m≤d i) {p:af A} (hp:p∈dO A d) :
   tag d hp∈Jy A m:= by
 classical
 induction hp using zt0 with
 | mem p hp =>
   obtain ⟨e,rfl⟩:=hp
   obtain ⟨f,hf⟩:=factors e.2
   have he : (∏ i,∏ x,gen i (f i x))=tag d (zBO ⟨e,rfl⟩) := by
     apply zkt
     simp only [cOd,hf,tag,stamp,zWu]
   obtain ⟨a,q,hq⟩:=d55 hz hd f
   rw [← he,hq,zDE]
   exact (Jy A m).mul_mem_left q (zCn ⟨a,rfl⟩)
 | zero =>
   have h:tag d ((dO A d).zero_mem)=0:=zkt (zhc (ztt d))
   rw [h]
   exact (Jy A m).zero_mem
 | add p q hp hq ihp ihq =>
   have h:tag d ((dO A d).add_mem hp hq)=tag d hp+tag d hq :=
     zkt (zrl (ztt d) p q)
   rw [h]
   exact (Jy A m).add_mem ihp ihq
 | smul c p hp ih =>
   have h:tag d ((dO A d).smul_mem c hp)=z12 _ (model A) c*tag d hp:= by
     apply zkt
     change ztt d (c•p)=(z12 (fZ A) (Ambient A) c)*ztt d p
     rw [← zd5,smul_monomial]
   rw [h]
   exact (Jy A m).mul_mem_left _ ih
end
end bzP
end
section
namespace cyu
noncomputable section
open aR dN rW aFT
open scoped BigOperators TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
private def ajm:af 4 →+ af 4 :=
 AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
  ((Finsupp.mapRange.addMonoidHom
    (zst :zM1 ao →ₗ[ao] zM1 ao).toAddMonoidHom).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
private theorem cF8 (U:af 4) (m:Fin 4 →₀ ℕ) :
 (ajm U).coeff m=zst (U.coeff m) :=rfl
private theorem dMd (U:af 4) :ajm U=lX U:= by
 classical
 apply MvPolynomial.ext
 intro m
 rw [cF8,lX,zqN]
 by_cases hm:m∈U.support
 · rw [zpa m hm]
   · simp
   · intro n _ hnm
     simp [z0I,hnm]
 · have hzero :U.coeff m=0:=Finsupp.notMem_support_iff.mp hm
   rw [hzero,zhc]
   symm
   apply zYF
   intro n hn
   have hnm:n≠m:= fun e=>hm (e ▸ hn)
   simp [z0I,hnm]
private def dL5:zvY ℤ (af 4) (af 4) :=
 Derivation.mk' ajm.toIntLinearMap (by
  intro U V
  classical
  change ajm (U*V)=U*ajm V+V*ajm U
  rw [zDE V (ajm U),zV6 (U*ajm V)]
  apply MvPolynomial.ext
  intro m
  simp only [AddMonoidAlgebra.coeff_add,zSs,zcz,
   cF8,zdo,Polynomial.derivative_mul,zfW])
private def bwm (i:Fin 3) :zvY ℤ (af 4) (af 4) :=
 (znf (z1z ((i.val+1 :ℕ) :ao))*z9v i.succ) •
   (zWe i.castSucc:zvY (zM1 ao) (af 4) (af 4)).restrictScalars ℤ
private def cbr :zvY ℤ (af 4) (af 4) :=
 dL5 + ∑ i:Fin 3,bwm i
private theorem eKF (U:af 4) :cbr U=pK U:= by
 have hsum: (∑ i:Fin 3,bwm i) U = ∑ i:Fin 3,bwm i U:= by
  change Derivation.coeFnAddMonoidHom (∑ i:Fin 3,bwm i) U= _
  rw [zdo,Finset.sum_apply]
  rfl
 rw [cbr,Derivation.add_apply,hsum,pK]
 change ajm U + _ = _
 rw [dMd]
 simp only [bwm,zep,zNe,zs5]
private def ceA (g:af 4) :zvY ℤ (af 4) (af 4) :=
 separant g•cbr -
  pK g •
   (zWe 3:zvY (zM1 ao) (af 4) (af 4)).restrictScalars ℤ
private theorem c6Y (g U:af 4) :ceA g U=u6 g U:= by
 simp only [ceA,u6,Derivation.sub_apply,zep,eKF,
  zNe,zs5,separant]
private theorem a5n {A B:Type*} [za6 A] [za6 B] [zZE A B]
  [zk2 A B] (d:zvY ℤ A A) :
  ∃ e :zvY ℤ B B,∀ a,e (z12 A B a)=z12 A B (d a) := by
 let f :=(Algebra.linearMap A B).comp d.liftKaehlerDifferential
 let l:=(f.liftBaseChange B).comp
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B).symm.toLinearMap
 refine ⟨l.compDer (zOb ℤ B),?_⟩
 intro a
 change l (zOb ℤ B (z12 A B a))= _
 simp [l,f,KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
private abbrev anD:=z3y (Fin 4) lN
private abbrev aYB:zdT (af 4) :=
 (nonZeroDivisors (zM1 ao)).map znf
private theorem bLH (U:af 4) :
  Q0 U=z12 anD PJ (z12 (af 4) anD U) := by
 simpa only [Q0,MvPolynomial.algebraMap_def] using
  (MvPolynomial.map_map (z12 (zM1 ao) lN)
    (z12 lN ale) U).symm
private theorem edz {k L σ:Type*} [za6 k] [za6 L]
  [zZE k L] [zk2 k L] :
  zk2 (z3y σ k) (z3y σ L) := by
 let A:=z3y σ k
 let B:=z3y σ L
 exact Algebra.FormallyEtale.of_equiv (A:=A ⊗[k] L)
  (Algebra.IsPushout.equiv k A L B)
private theorem fVj {k L T:Type*} [zrb k] [zrb L] [zZE k L]
   [zw7 k L] [za6 T] [ztn T] [zZE k T] :
   IsReduced (T ⊗[k] L) := by
 let F:=zNv T
 apply IsReduced.tensorProduct_of_flat_of_forall_fg
 intro B hB
 have :zw7 k B :=
   Subalgebra.isSeparable_iff.mpr (fun x _=>zMb k x)
 have :zVK k B :=
   ⟨fun x=>(zMb k x).isIntegral⟩
 let:zrb B:=(isField_of_isIntegral_of_isField' (S:=B) (Field.toIsField k)).toField
 have :zUK k B:=(Subalgebra.fg_iff_finiteType B).mp hB
 have :Algebra.FormallyUnramified k B:=Algebra.FormallyUnramified.of_isSeparable k B
 have :IsReduced (F ⊗[k] B) :=Algebra.FormallyUnramified.isReduced_of_field F _
 let f :=zE2 k T F
 exact znD (Algebra.TensorProduct.map f (AlgHom.id k B))
   (Module.Flat.rTensor_preserves_injective_linearMap (M:=B) f.toLinearMap
     (zxb T F))
private theorem fSQ {k L A B:Type*} [zrb k] [zrb L] [zZE k L]
   [zw7 k L] [za6 A] [za6 B] [zZE k A] [zZE k B]
   [zZE L B] [zZE A B] [zsf k L B] [zsf k A B]
   [Algebra.IsPushout k L A B] (p:znc A) [p.IsPrime] :
   (p.map (z12 A B)).IsRadical:= by
 rw [Ideal.isRadical_iff_quotient_reduced]
 let T:=A ⧸ p
 have :IsReduced (T ⊗[k] L) :=fVj (k :=k) (L:=L) (T:=T)
 let e :=(zeK B p).toRingEquiv.trans
   ((Algebra.IsPushout.cancelBaseChangeAlg k L A B T).toRingEquiv.trans
     (Algebra.TensorProduct.comm k L T).toRingEquiv)
 exact znD e e.injective
private theorem cqx {A B:Type*} [za6 A] [za6 B] [zZE A B]
   (d:zvY ℤ A A) (D:zvY ℤ B B)
   (hd : ∀ a,D (z12 A B a)=z12 A B (d a))
   (p:znc A) (hp : ∀ x∈p,d x∈p) :
   ∀ x∈p.map (z12 A B),D x∈p.map (z12 A B) := by
 let J:=p.map (z12 A B)
 intro x hx
 refine zt0 (p:= fun x _=>D x∈J) ?_ ?_ ?_ ?_ hx
 · rintro _ ⟨a,ha,rfl⟩
   rw [hd]
   exact z7X _ (hp a ha)
 · simp [J]
 · intro a b _ _ ha hb
   rw [zrl]
   exact J.add_mem ha hb
 · intro b a ha hDa
   rw [zs5,D.leibniz,zs5,zs5]
   exact J.add_mem (J.mul_mem_left b hDa) (J.mul_mem_right (D b) ha)
private theorem guB {A B:Type*} [za6 A] [za6 B] [zZE A B]
    [zVK A B] (d:zvY ℤ A A) (D:zvY ℤ B B)
    (hd : ∀ a,D (z12 A B a)=z12 A B (d a))
    (q:znc B) [q.IsPrime] (hrad: ((q.under A).map (z12 A B)).IsRadical)
    (hp : ∀ x∈q.under A,d x∈q.under A) : ∀ x∈q,D x∈q:= by
  let J:=(q.under A).map (z12 A B)
  have hmin:q∈J.minimalPrimes :=Ideal.IsIntegral.mem_minimalPrimes_map_under (R:=A) q
  let C:=zhy q
  have hloc:J.map (z12 B C)=q.map (z12 B C) := by
    calc
      _=J.radical.map (z12 B C) :=
        zPw (Ideal.map (z12 B C)) hrad.radical.symm
      _=(J.map (z12 B C)).radical:=IsLocalization.map_radical q.primeCompl C J
      _ = _:=z8P (A:=C) q J hmin
  intro u hu
  have hm:z12 B C u∈J.map (z12 B C) := by
    rw [hloc]
    exact z7X _ hu
  obtain ⟨s,hs,hsu⟩:=(IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl C J u).mp hm
  have hDsu:=cqx d D hd _ hp _ hsu
  have hmem:D (s*u)∈q:=Ideal.map_comap_le hDsu
  rw [D.leibniz,zs5,zs5] at hmem
  exact (‹q.IsPrime›.mem_or_mem
    ((q.add_mem_iff_left (q.mul_mem_right (D s) hu)).mp hmem)).resolve_left hs
private theorem guC {A B:Type*} [za6 A] [za6 B] [zZE A B]
  (M:zdT A) [zNo M B] (d:zvY ℤ B B) (p:znc B)
  (h : ∀ a,z12 A B a∈p→d (z12 A B a)∈p) :
  ∀ x∈p,d x∈p:= by
 intro x hx
 obtain ⟨⟨a,s⟩,he⟩:=zg4 M x
 have hs :IsUnit (z12 A B s) :=z0j B s
 have ha :z12 A B a∈p:=he ▸ p.mul_mem_right _ hx
 have hdxs :d (x*z12 A B s)∈p:=he.symm ▸ h a ha
 rw [d.leibniz,zs5,zs5] at hdxs
 exact (p.unit_mul_mem_iff_mem hs).mp ((p.add_mem_iff_right (p.mul_mem_right _ hx)).mp hdxs)
theorem proof :aFT.c2 := by
 intro g aI hprime hI
 have :zk2 (af 4) anD :=
   Algebra.FormallyEtale.of_isLocalization (Rₘ:=anD) aYB
 have :zk2 lN ale :=
   Algebra.FormallyEtale.of_isSeparable lN ale
 have :zk2 anD PJ:=edz
 obtain ⟨d,hd⟩:=a5n (B:=anD) (ceA g)
 obtain ⟨D,hD⟩:=a5n (B:=PJ) d
 let q:=aI.comap Ow
 have :q.IsPrime :=hprime.comap Ow
 have hraw (U:af 4) :D (Q0 U)= Q0 (u6 g U) := by
   rw [bLH,hD,hd]
   exact (zPw (fun a :af 4=>z12 anD PJ
     (z12 (af 4) anD a)) (c6Y g U)).trans (bLH _).symm
 let p:=q.under anD
 have :p.IsPrime :=zG1 _ _
 have hrad: (p.map (z12 anD PJ)).IsRadical :=
   fSQ (k :=lN) (L:=ale) p
 refine ⟨D,hraw,guB (A:=anD) (B:=PJ) d D hD q hrad ?_⟩
 apply guC aYB d p
 intro U hU
 have hUgeo:bC U∈aI:= by
   rw [← aQd,bLH]
   exact hU
 have hflow:z12 (af 4) anD (u6 g U)∈p:= by
   change Ow (z12 anD PJ
     (z12 (af 4) anD (u6 g U)))∈aI
   rw [← bLH,aQd]
   exact hI U hUgeo
 rw [hd]
 exact (zPw (z12 (af 4) anD) (c6Y g U)).symm ▸ hflow
end
end cyu
end
section
set_option backward.isDefEq.respectTransparency false
namespace bRN
noncomputable section

open aeF (Os)
open XX (EO aoG ad4)
open Polynomial
open scoped Polynomial WithZero
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
private theorem normalize (w:zfZ F ℤᵐ⁰) (hw:w.IsNontrivial)
   (hk :w.IsTrivialOn k) :
   ∃ p:zGX k F,p.value.IsEquiv w∧(zpX w→p.value=w) := by
 let:w.IsNontrivial:=hw
 let:w.IsRankOneDiscrete :=Valuation.IsRankOneDiscrete.mk' w
 let e :=Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w
 let f :=e.toMonoidWithZeroHom
 have hmono:StrictMono f :=
   Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono w
 let v :=w.restrict.map f hmono.monotone
 have he :v.IsEquiv w :=
   (Valuation.isEquiv_map_self_of_strictMono f hmono).trans w.isEquiv_restrict.symm
 let p:zGX k F :=
   { value :=v
     normalized:=e.surjective.comp (MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _)
     on_constants :=(he.symm.isTrivialOn hk).eq_one }
 refine ⟨p,he,fun hs=>Valuation.ext fun x => ?_⟩
 exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hs x
section Extension
local instance :zZE (ziC k) (ziC F) :=Os k (F:=F)
private theorem c3S (a :k) :
  z12 (ziC k) (ziC F) (ztW a)=ztW (z12 k F a) := by
 simpa only [zrL,zyJ] using
  (ad4 (F:=F) (z1z a))
private theorem eKU :
  z12 (ziC k) (ziC F) zyX=RatFunc.X:= by
 simpa only [zSo,zYR] using
  (ad4 (F:=F) (z7y:k[X]))
private theorem bLs {L:Type} [zrb L] (w:zfZ L ℤᵐ⁰)
   (z :w.valuationSubring) :
   zeo w.valuationSubring z=0↔w (z :L)<1 :=
 (IsLocalRing.residue_eq_zero_iff z).trans w.mem_maximalIdeal_iff
private theorem efg (p:zGX k F)
   (q:zGX (ziC k) (ziC F))
   (he :p.value.IsEquiv (q.value.comap ztW))
   [zQO k (EO p)] (P:F[X]) :
   q.value (z12 F[X] (ziC F) P) =
     P.support.sup (fun i=>q.value (ztW (P.coeff i))) := by
 classical
 let A:=p.value.valuationSubring
 let B:=q.value.valuationSubring
 let ι:A →+* B:=(RatFunc.C.comp A.subtype).codRestrict B.toSubring
   (fun z=>he.le_one_iff_le_one.mp z.2)
 let:IsLocalHom ι:=⟨fun z hz=> by
   apply ((z9W p.value).isUnit_iff_valuation_eq_one).mpr
   exact he.eq_one_iff_eq_one.mpr
     (((z9W q.value).isUnit_iff_valuation_eq_one).mp hz)⟩
 let e :EO p →+* EO q:=IsLocalRing.ResidueField.map ι
 let:zZE (EO p) (EO q) :=e.toAlgebra
 let:zZE k (EO q) :=(e.comp (z12 k (EO p))).toAlgebra
 let:zsf k (EO p) (EO q) :=
   zsL fun _=>rfl
 let r :ziC k →+* EO q:=(zeo B).comp (aoG q)
 have hr : (z12 k (EO q)).comp (zz4 k) =
     r.comp (z12 k (ziC k)) := by
   ext a
   change e (zeo A (aoG p a)) =
     zeo B (aoG q (z12 k (ziC k) a))
   dsimp only [e]
   rw [IsLocalRing.ResidueField.map_residue]
   apply zPw (zeo B)
   apply zkt
   change ztW (z12 k F a) =
     z12 (ziC k) (ziC F) (z12 k (ziC k) a)
   rw [z4W,c3S]
 let x :B:=aoG q (zyX:ziC k)
 have hx : (x :ziC F)=RatFunc.X:=eKU
 have ht:znN k (zeo B x) :=
   RatFunc.transcendental_X.ringHom_of_comp_eq (f :=zz4 k) (g:=r)
     (fun a=>⟨a,rfl⟩) r.injective hr
 let:Algebra.IsAlgebraic k (EO p) :=Algebra.IsAlgebraic.of_finite _ _
 have ht' : znN (EO p) (zeo B x) :=
   (Algebra.IsAlgebraic.transcendental_iff k (EO p)).mp ht
 obtain rfl | hP:=eq_or_ne P 0
 · simp
 obtain ⟨m,hm,hmax⟩:=zOU P.support
   (Polynomial.support_nonempty.mpr hP) (fun i=>q.value (ztW (P.coeff i)))
 let b:=P.coeff m
 have hb:b≠0:=mem_support_iff.mp hm
 have hvb:0<q.value (ztW b) :=q.value.pos_iff.mpr ((zyg ztW).2 hb)
 have hd (i:ℕ) :p.value (P.coeff i/b)≤1 := by
   apply he.le_one_iff_le_one.mpr
   change q.value (ztW (P.coeff i/b))≤1
   rw [map_div₀,q.value.map_div,div_le_one₀ hvb]
   by_cases hi:i∈P.support
   · exact (zZi (f := fun j=>q.value (ztW (P.coeff j))) hi).trans_eq hmax
   · simp [notMem_support_iff.mp hi]
 let d (i:ℕ) :A:=⟨P.coeff i/b,hd i⟩
 let S:A[X] := ∑ i∈P.support,monomial i (d i)
 have hcoeff :S.coeff m=d m:= by
   simp [S,zaW,coeff_monomial,hm]
 have hdm:d m=1 :=zkt (div_self hb)
 let T:=S.map (zeo A)
 have hT:T≠0:= by
   intro h
   have hh:T.coeff m=1 := by simp [T,hcoeff,hdm]
   simp [h] at hh
 let z :B:=S.eval₂ ι x
 have hz :zeo B z=zEU (zeo B x) T:= by
   dsimp only [z,T]
   rw [zly,zCD,Polynomial.eval₂_map]
   congr 1
 have hzval :q.value (z :ziC F)=1 := by
   refine zWs z.2 (zHm fun hlt=>hT ?_)
   have hzero :=(bLs q.value z).mpr hlt
   rw [hz] at hzero
   exact (transcendental_iff_injective.mp ht') (by simpa using hzero)
 have hscale :z12 F[X] (ziC F) P=ztW b*(z :ziC F) := by
   have hpoly :z12 F[X] (ziC F) P=P.eval₂ ztW RatFunc.X:= by
     rw [← RatFunc.aeval_X_left_eq_algebraMap,zCD,z4W]
   rw [hpoly,eval₂_eq_sum,sum_def]
   change _=ztW b*B.subtype (S.eval₂ ι x)
   rw [zly]
   change _=ztW b*S.eval₂ (RatFunc.C.comp A.subtype) (x :ziC F)
   rw [hx]
   simp only [S,eval₂_finsetSum,eval₂_monomial,Finset.mul_sum]
   apply zUo rfl
   intro i _
   change _=ztW b*(ztW (P.coeff i/b)*zyX ^i)
   rw [← ztg,← zok,mul_div_cancel₀ _ hb]
 rw [hscale,zok,hzval,zqe]
 exact hmax.symm
private theorem fXj (q:zGX (ziC k) (ziC F))
   (h : ∀ P:F[X],q.value (z12 F[X] (ziC F) P) =
     P.support.sup (fun i=>q.value (ztW (P.coeff i)))) :
   zpX (q.value.comap ztW) := by
 classical
 have hpoly (P:F[X]) :
     ∃ a :F,q.value (ztW a)=q.value (z12 F[X] (ziC F) P) := by
   obtain rfl | hp:=eq_or_ne P 0
   · exact ⟨0,by simp⟩
   obtain ⟨i,_,hi⟩:=zOU P.support
     (Polynomial.support_nonempty.mpr hp) (fun i=>q.value (ztW (P.coeff i)))
   exact ⟨P.coeff i,hi.symm.trans (h P).symm⟩
 intro γ
 obtain ⟨y,rfl⟩:=q.normalized γ
 induction y using zSH with
 | _ P Q _ =>
   obtain ⟨a,ha⟩:=hpoly P
   obtain ⟨b,hb⟩:=hpoly Q
   refine ⟨a/b,?_⟩
   change q.value (ztW (a/b))= _
   rw [map_div₀,q.value.map_div,q.value.map_div,ha,hb]
end Extension
theorem proof :XX.c5:= by
 intro k F _ _ _ hres q
 let:zZE (ziC k) (ziC F) :=Os k (F:=F)
 by_cases h : ∀ x :F,q.value (ztW x)≤1
 · exact Or.inl h
 right
 obtain ⟨x,hx⟩:=not_forall.mp h
 have hx' := lt_of_not_ge hx
 let w:=q.value.comap ztW
 have hw:w.IsNontrivial:=⟨⟨x,(zero_lt_one.trans hx').ne',hx'.ne'⟩⟩
 have hk :w.IsTrivialOn k :=⟨fun a ha=> by
   change q.value (ztW (z12 k F a))=1
   rw [← c3S]
   exact q.on_constants _ ((zyg ztW).2 ha)⟩
 obtain ⟨p,he,hp⟩:=normalize w hw hk
 let:zQO k (EO p) :=hres p
 have hG:=efg p q he
 have hw' := hp (fXj q hG)
 have hcoeff (a :F) :p.value a=q.value (ztW a) :=
   zmU hw' a
 refine ⟨p,fun P => ?_⟩
 simpa only [hcoeff] using hG P
end
end bRN
end
section
namespace aFQ
noncomputable section
open aR oR we aeC Polynomial
theorem b9C {j:ℕ} (hj:0<j) (hp:j<K1.p) : (j:ao)≠0:= by
 intro h
 have hk : (j:K1.K)=0:=embed.injective (by simpa only [zGu,zhc] using h)
 exact (Nat.not_dvd_of_pos_of_lt hj hp) ((zX2 K1.K K1.p _).mp hk)
section
variable {f :af 3} {P:znc (eT 3)} (h:aqG f P)
local notation "e" => KM f P
local notation "r" => azj f P
local notation "s" => e (separant f)
local notation "d" => delta h
theorem bD2 (a :ao) :d (zsm e a)=0:= by
 change d (e (znf (z1z a)))=0
 rw [cKh,derivative_C,zhc,zhc]
private theorem b0g (n:ℕ) :d (n:Chart f P)=0:= by
 rw [← zGu (zsm e)]
 exact bD2 h _
theorem dVV:d (e (znf z7y))=1 := by
 rw [cKh,derivative_X,zXs,zXs]
private theorem dVW:d r = -(r*r*d s) := by
 have hh:=aT8 h s r
 have hd1 :d (1 :Chart f P)=0:= by
  simpa only [z4o] using b0g h 1
 rw [aXF,hd1] at hh
 linear_combination r*hh.symm - d r*aXF f P
private theorem dVX (n:ℕ) :d (r^n) = -(n:Chart f P)*(r^(n+1))*d s := by
 induction n with
 | zero=>simpa using (b0g h 1)
 | succ n ih =>
   rw [zVI r n,aT8,dVW,ih,zVI r (n+1),zVI r n]
   push_cast
   ring
private theorem dVY (b:af 3) (n:ℕ) :
    d (e b*r^n) =
      e (zsz f*Ev f b -
        (n:af 3)*b*Ev f (zsz f))*r^(n+2) := by
  rw [aT8,dVX,aT7 h (zsz f),aT7 h b,
    zpO,zok,zok,zok,zGu,zVI r (n+1),zVI r n]
  have hsr :s*r=1 :=aXF f P
  linear_combination
    - (e (Ev f b)*r^n*r)*hsr
private theorem eo7 {n:ℕ} (hn:n+1<K1.p) :
  (n+1 :ao)*(((n+1).factorial:ao)⁻¹)=(n.factorial:ao)⁻¹:= by
 have hs : (n+1 :ao)≠0:= by
  exact_mod_cast b9C (Nat.succ_pos n) hn
 rw [zwO,z2R,zg0,mul_inv_rev]
 rw [mul_rotate',inv_mul_cancel₀ hs,zqe]
theorem bro (n:ℕ) (hn:n<bf) :
    d (Ub f P n)=(n+1 :ℕ)*Ub f P (n+1) := by
  rcases n with _ | _ | _ | k
  · simp [Ub,aT7,Ev,D3,
      cFY,zYE,← ztg,
      zDE r s,aXF]
  · simp [Ub,aT7,Ev,D3,
      cFY,zYE,map_ofNat]
    have hsr :r*s=1 :=(zDE s r).symm.trans (aXF f P)
    linear_combination (2*e (z9v 2))*hsr
  · have hsc: (3:ao)*(2*((6:ao)⁻¹))=1 := by
      have hn: (6:ao)≠0:=b9C (j:=6) (by decide) (by decide)
      rw [← ztg,show (3:ao)*2=6 by norm_num,mul_inv_cancel₀ hn]
    have hc:=zPw (zsm e) hsc
    simp only [zok,map_ofNat,zXs] at hc
    have ht:Ev f (z9v 2) = -D3 f := by
      simp [Ev,D3,zYE]
    change d (Ub f P 2)=((3:ℕ) :Chart f P)*Ub f P 3
    simp only [Ub,aT7,ht,AR,map_neg,Nat.cast_ofNat]
    norm_num [Nat.factorial]
    linear_combination -(e (D3 f)*r)*hc
  · have hn' : k+3+1<K1.p:= by
      change k+3<133672 at hn
      change k+3+1<2130706433
      omega
    have hc:=zPw (zsm e) (eo7 hn')
    simp only [zok,zrl,zGu,zXs] at hc
    change d (2*e (AR f k) *
        zsm e (((k+3).factorial:ao)⁻¹)*r^(2*k+1)) =
      (k+3+1 :ℕ)*(2*e (AR f (k+1)) *
        zsm e (((k+3+1).factorial:ao)⁻¹)*r^(2*(k+1)+1))
    have hconst:d (2*zsm e (((k+3).factorial:ao)⁻¹))=0:= by
      have hd2 :d (2 :Chart f P)=0:=b0g h 2
      rw [aT8,bD2,hd2,znR,z1S,z0a]
    rw [show 2*e (AR f k) *
        zsm e (((k+3).factorial:ao)⁻¹)*r^(2*k+1) =
        (2*zsm e (((k+3).factorial:ao)⁻¹)) *
          (e (AR f k)*r^(2*k+1)) by ring,
      aT8,hconst,z1S,z0a,dVY]
    rw [show 2*k+1+2=2*(k+1)+1 by omega]
    change _ *(e (AR f (k+1))*_)= _
    push_cast at hc ⊢
    linear_combination-(2*e (AR f (k+1))*r^(2*(k+1)+1))*hc
theorem dSS (hc:BW f≤P) :Ub f P bf=0:= by
 have hcut:fW (Dm f)∈P:=hc (zCn (by simp))
 have hz :e (Dm f)=0:=bm2 f P hcut
 change 2*e (Dm f)*_ *_=0
 rw [hz,znR,z1S,z1S]
theorem bCW {A:Type*} [Semiring A] (M:ℕ) (a :ℕ→A)
   (n:ℕ) : (aon M a).coeff n=if n<M then a n else 0:= by
 classical
 rw [aon,zaW]
 split_ifs with hn
 · rw [zi6 (⟨n,hn⟩:Fin M)]
   · exact coeff_monomial_same _ _
   · intro i _ hi
     exact coeff_monomial_of_ne _ (fun he=>hi (Fin.ext he.symm))
   · simp
 · exact zYF fun i _ =>
     coeff_monomial_of_ne _ (fun he=>hn (he.symm ▸ i.isLt))
theorem dGI (hc:BW f≤P) (n:ℕ) :
   d ((aMK f P).coeff n)=(aMK f P).derivative.coeff n:= by
 rw [coeff_derivative,aMK,bCW,bCW]
 by_cases hn:n+1<bf
 · rw [zYo (by omega),zYo hn,bro h n (by omega),zDE,z6H,z4o]
 · rw [zNB hn,z1S]
   split_ifs with hlt
   · rw [bro h n hlt,show n+1=bf by omega,dSS hc,znR]
   · exact zhc _
end
end
end aFQ
end
section
namespace aFQ
noncomputable section
open aR oR we aeC Polynomial
private theorem b5P {A:Type*} [za6 A] (i j:ℕ) (U:A[X]) :
  z75 i (z75 j U)=z75 j (z75 i U) := by
 have hi:=z5U (hasseDeriv_comp (R:=A) i j) U
 have hj:=z5U (hasseDeriv_comp (R:=A) j i) U
 simp only [zoD,LinearMap.smul_apply] at hi hj
 rw [hi,hj,zg2 j i,Nat.choose_symm_add (a :=i) (b:=j)]
section DifferentialPolynomials
variable {A:Type*} [za6 A]
variable (D:A →+ A) (hOne :D 1=0)
 (hMul : ∀ a b,D (a*b)=a*D b+D a*b)
private def Oj:Subsemiring A[X] where
 carrier := {U | ∀ n,D (U.coeff n)=U.derivative.coeff n}
 zero_mem' n:= by simp
 one_mem' n:= by
  rw [derivative_one,zO6,coeff_one]
  split_ifs
  · exact hOne
  · exact zhc _
 add_mem' {U V} hU hV n:= by
  simp only [z7l,zrl,hU n,hV n]
 mul_mem' {U V} hU hV n:= by
  change D ((U*V).coeff n)=(U*V).derivative.coeff n
  simp only [coeff_mul,zdo,hMul,hU _,hV _,derivative_mul,z7l,
    zfW]
  abel
local notation "H" => Oj D hOne hMul
private theorem b5Q {U:A[X]} (hU:U∈H) (i:ℕ) :
  z75 i U∈H := by
 have hNat (n:ℕ) :D (n:A)=0:= by
  induction n with
  | zero=>simp
  | succ n ih=>rw [Nat.cast_succ,map_add,ih,hOne,add_zero]
 intro n
 rw [← hasseDeriv_one',b5P 1 i,hasseDeriv_one',hasseDeriv_coeff,
  hasseDeriv_coeff,hMul,hNat,hU (n+i),z1S,z0a]
private theorem gqz (k :ao →+* A) (hk : ∀ z,D (k z)=0)
   (x₀:A) (hx :D x₀=1) (b:ao[X]) :taylor x₀ (b.map k)∈H := by
 have hX: ((z7y:A[X])+Polynomial.C x₀)∈H := by
   intro n
   simp only [z7l,derivative_X_add_C,coeff_X,coeff_C,coeff_one]
   split_ifs with hn hn' <;> simp_all
 induction b using zCU with
 | add a b ha hb=>simpa only [Polynomial.map_add,map_add] using (H).add_mem ha hb
 | monomial n a =>
   rw [zAZ,taylor_monomial]
   refine (H).mul_mem (fun j => ?_) ((H).pow_mem hX n)
   simp only [coeff_C,derivative_C,zO6]
   split_ifs <;> simp [hk]
private theorem b55 {R:A[X]} (hR:R∈H)
    (h0:R.coeff 0=0) (hdeg:R.natDegree<K1.p)
    (hUnit : ∀ n:ℕ,0<n→n<K1.p→ IsUnit (n:A)) :R=0:= by
  have hz : ∀ n<K1.p,R.coeff n=0:= by
    intro n
    induction n with
    | zero=>exact fun _=>h0
    | succ n ih =>
      intro hn
      have hstep:=hR n
      rw [coeff_derivative,ih (Nat.lt_of_succ_lt hn),zhc] at hstep
      have hu:IsUnit ((n:A)+1) := by
        simpa only [z6H,z4o] using hUnit (n+1) (Nat.succ_pos n) hn
      exact hu.mul_left_inj.mp (hstep.symm.trans (z1S _).symm)
  ext n
  rw [zO6]
  by_cases hn:n<K1.p
  · exact hz n hn
  · exact zQl (hdeg.trans_le (Nat.le_of_not_lt hn))
include hOne hMul in
private theorem cTd (k :ao →+* A) (hk : ∀ z,D (k z)=0)
   (x₀:A) (hx :D x₀=1) (f :af 3) (U W:A[X]) (hShift:taylor x₀ U=W)
   (hW : ∀ n,D (W.coeff n)=W.derivative.coeff n)
   (hEval : (jW k f U).eval x₀=0) (hDeg: (jW k f U).natDegree<K1.p)
   (hUnit : ∀ n:ℕ,0<n→n<K1.p→ IsUnit (n:A)) :
   jW k f U=0:= by
 let t:=(taylorAlgHom x₀).toRingHom
 let g:=t.comp (zhd k)
 let a :Fin 3→ A[X] := fun i=>z75 i.val W
 have hArg (i:Fin 3) :t (z75 i.val U)=a i:= by
   change taylor x₀ (z75 i.val U)=z75 i.val W
   rw [← hasseDeriv_taylor,hShift]
 have hT:t (jW k f U)=zSZ g a f := by
   rw [jW,zUe]
   simp only [hArg]
   rfl
 have hR:t (jW k f U)∈H := by
   rw [hT]
   let g' : ao[X] →+* H :=g.codRestrict _ (gqz D hOne hMul k hk x₀ hx)
   let v :Fin 3→H := fun i=>⟨a i,b5Q D hOne hMul hW i.val⟩
   let R' : H :=zSZ g' v f
   have hm: (R' : A[X])=zSZ g a f :=
     zUe f g' (H).subtype v
   rw [← hm]
   exact R'.2
 apply (taylor_eq_zero x₀ _).mp
 apply b55 D hOne hMul hR _ _ hUnit
 · change (taylor x₀ (jW k f U)).coeff 0=0
   rwa [taylor_coeff_zero]
 · change (taylor x₀ (jW k f U)).natDegree<K1.p
   rwa [natDegree_taylor]
end DifferentialPolynomials
section
variable {f :af 3} {P:znc (eT 3)}
local notation "A" => Chart f P
local notation "e" => KM f P
local notation "k" => constants e
local notation "x₀" => e (MvPolynomial.C Polynomial.X)
private theorem eor (i:Fin 3) :
  (z75 i.val (aot f P)).eval x₀=e (z9v i) := by
 have hi:i.val<bf :=i.isLt.trans (by decide)
 rw [← taylor_coeff,aot,taylor_taylor,add_neg_cancel,taylor_zero,aMK,
  bCW,zYo hi]
 fin_cases i <;> rfl
private theorem cVh (hc:BW f≤P) :
   (jW k f (aot f P)).eval x₀=0:= by
 unfold jW
 change (zhz x₀) (zSZ _ _ f)= _
 have hCoeff : (zhz x₀).comp (zhd k)=(e).comp MvPolynomial.C:= by
   apply z86
   · intro z
     change ((z1z z).map k).eval x₀=k z
     rw [zrL,zFf]
   · change ((z7y:ao[X]).map k).eval x₀=x₀
     rw [zSo,eval_X]
 rw [zUe,hCoeff]
 simp only [coe_evalRingHom,eor]
 have he :=(zUe f znf e z9v).symm
 rw [MvPolynomial.eval₂_eta] at he
 rw [he]
 exact bm2 f P (hc (zCn (by simp)))
end
end
end aFQ
end
section
namespace aFQ
noncomputable section
open aR oR we aeC Polynomial
section
variable {f :af 3} {P:znc (eT 3)} {y :Fin 3→cH}
private def specialize (hy :y∈D7 f P) :Chart f P →+* cH :=
 aGX (Bt y) (fun b hb=>hy.1 (fW b) hb) (isUnit_iff_ne_zero.mpr hy.2)
private theorem bOf (hy :y∈D7 f P) (b:af 3) :
  specialize hy (KM f P b)=Bt y b :=
 cE7 _ _ _ b
private theorem gtW (hy :y∈D7 f P) :
  specialize hy (azj f P)=(Bt y (zsz f))⁻¹:= by
 have hh:=zPw (specialize hy) (aXF f P)
 simp only [zok,zXs,bOf] at hh
 exact ((mul_eq_one_iff_inv_eq₀ hy.2).mp hh).symm
private theorem de5 (hy :y∈D7 f P) :
  (specialize hy).comp (zsm (KM f P))=z12 ao cH := by
 apply zz5
 intro a
 change specialize hy (KM f P (znf (z1z a)))= _
 rw [bOf]
 change zY9 y (zDK qY (znf (z1z a)))= _
 rw [zpw,MvPolynomial.eval_C,← zrD]
 rfl
private theorem gtX (hy :y∈D7 f P) (j:ℕ) :
    specialize hy (Ub f P j)=afk f (Bt y) j:= by
  rcases j with _ | _ | _ | n
  all_goals simp only [Ub,afk,bOf,zok,map_ofNat,zkq,
    gtW]
  change 2*Bt y (AR f n) *
      ((specialize hy).comp (zsm (KM f P))) (((n+3).factorial:ao)⁻¹) *
        (Bt y (zsz f))⁻¹^(2*n+1)= _
  rw [de5 hy,map_inv₀,zGu,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring
private theorem cqu (hy :y∈D7 f P) :
  (aot f P).map (specialize hy)=aac f (Bt y) := by
 simp only [aot,aac,map_taylor,map_neg,bOf,centre,aMK,aon,
  Polynomial.map_sum,zAZ,gtX]
private theorem dfd (hy :y∈D7 f P) :
   (jW (zsm (KM f P)) f (aot f P)).map (specialize hy) =
     Of f (aac f (Bt y)) := by
 unfold jW
 change zhd (specialize hy) (zSZ _ _ _)= _
 rw [zUe,Polynomial.mapRingHom_comp,de5]
 simp only [zKC,← zvc,cqu]
 unfold Of
 rw [znM]
end
end
end aFQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace aF0
noncomputable section
open K1 cu qQ MN ana Polynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ g:IW,Irreducible g→0<g.natDegree →
    ∃ f :aR.af 2,f.totalDegree≤total g∧f.degreeOf 1≤g.natDegree ∧
      u7 f≠0∧(zye {u7 f}).IsPrime ∧
      ∀ S:K[X],cBx S g=0→cBx S g.derivative≠0 →
        oR.qg 1 f (aR.extend S)
def c2 :Prop :=
  ∀ (f :aR.af 2) (d b j:ℕ),2≤d→d<180265→0<j →
    f.totalDegree≤b→f.degreeOf 1≤j→Nonempty (dmu f d b j)
end
end aF0
end
section
namespace czH
noncomputable section
open K1 oR ana aF0 Polynomial PolynomialDifferential
open aR (ao af cK embed jet)
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem auQ (S:ao[X]) : (S.map zvZ).eval zZJ=asx S:= by
 rw [Polynomial.eval_map]
 change zqf zvZ zZJ S=asx S
 congr 1
 apply z86
 · intro a
   simp [zvZ]
 · simp [zZJ]
private theorem aQw (f :af 2) (S:ao[X]) :
  zho (flatten f) S=cK f S:= by
 let x :zNO (Fin 2)→ao[X] := fun
  | none=>Polynomial.X
  | some i=>jet S i
 have h:=MvPolynomial.aeval_optionEquivRight_symm (R:=ao) x f
 have hx :x none=Polynomial.X:=rfl
 have hj: (fun i=>x (some i))=jet S:=rfl
 rw [hx,hj,Polynomial.aeval_X_left] at h
 rw [show (AlgHom.id ao ao[X]).toRingHom=zz4 (ao[X]) from rfl,
  MvPolynomial.map_id,MvPolynomial.aeval_eq_eval] at h
 unfold flatten at *
 unfold cK zho
 refine (AlgHom.congr_fun ?_ _).trans h
 apply zpH
 intro v
 rw [differentialSpecializationHom,zTw,zTw]
 cases v <;> rfl
private theorem dw {f :af 2} {S:ao[X]} {d:ℕ}
   (hd:d<180265) (hD:S.natDegree≤d) (hS:qg 1 f S) (x y :ao) :
   zIe (Ia S)
     (taylorAgreementEquation zZJ (bY f) (d+1) (power d) (zvZ x) (zvZ y))
     = 0↔S.eval x=y := by
 have hsol:zho (bY f) (S.map zvZ)=0:= by
   rw [bY,← map_differentialSpecialization,aQw,hS.1,zgY]
 have hsf :zho (z92 (flatten f) 1) S≠0:= by
   change zho
     (zWe (some 1) ((MvPolynomial.optionEquivRight ao (Fin 2)).symm f)) S≠0
   rw [← MvPolynomial.optionEquivRight_symm_pderiv]
   exact (aQw (zWe 1 f) S).substr hS.2
 have hsep:jetEvaluation (z92 (bY f) (Fin.last 1))
     zZJ (Ia S)≠0:= by
   change jetEvaluation (z92 (bY f) 1) zZJ (Ia S)≠0
   rw [Ia,← eval_differentialSpecialization,bY,← map_separant,
     ← map_differentialSpecialization,auQ]
   exact fun he=>hsf (bhW (he.trans (zhc _).symm))
 have hdeg: (S.map zvZ).degree<((d+1 :ℕ) :WithBot ℕ) := by
   have hb: (S.map zvZ).natDegree≤d:=Polynomial.natDegree_map_le.trans hD
   exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast zB1 hb)
 have hcharG:CharP ao K1.p:=zgG embed.injective K1.p
 have :CharP Tv K1.p:=zgG constants.injective K1.p
 have hpiv : ∀ i:ℕ,1< i→i<d+1→(i.choose 1 :Tv)≠0:= by
   intro i hi ht
   rw [zk3]
   intro hz
   have hp:=Nat.le_of_dvd (by omega :0< i)
     ((zX2 Tv K1.p i).mp hz)
   change 2130706433≤ i at hp
   omega
 rw [taylorAgreementEquation_eq_zero_iff zZJ (bY f) (τ:=power d)
     (zH5 d) (Ia S)
     (by rwa [aeval_initialJetSeparant]) (zvZ x) (zvZ y)]
 rw [Ia,rationalTaylorPolynomial_polynomialJet zZJ (bY f) (S.map zvZ)
   hsol hsep hdeg hpiv,zdm,constants.injective.eq_iff]
theorem proof :aF0.c2 := by
  intro f d b j _hd₀ hd hj hb htop
  let cut (x y :K) :=
    taylorAgreementEquation zZJ (bY f) (d+1) (power d)
      (zvZ (embed x)) (zvZ (embed y))
  have hτ:TaylorExponentSufficient 1 (d+1) (power d) :=
    zH5 d
  have htotal (x y :K) : (cut x y).totalDegree≤BJ d b:= by
    refine (totalDegree_taylorAgreementEquation_le zZJ (bY f) hτ _ _).trans ?_
    rw [rationalTaylorCutDegreeBound,BJ]
    exact z3b (Nat.mul_le_mul_left (power d)
      (Nat.sub_le_sub_right ((adr f).trans hb) 1)) 1
  refine ⟨⟨cut,htotal,?_,?_⟩⟩
  · intro x y
    apply le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (htotal x y))
    simpa only [z2h] using
      degreeOf_taylorAgreementEquation_firstOrder_le zZJ (bY f) j (d+1) (power d)
        hτ hj ((aCA f).trans htop) (zvZ (embed x)) (zvZ (embed y))
  · intro S hD hS x y
    simpa only [zdm,embed.injective.eq_iff] using
      dw hd (Polynomial.natDegree_map_le.trans hD) hS (embed x) (embed y)
end
end czH
end
section
set_option backward.isDefEq.respectTransparency false
namespace czD
noncomputable section
open aeF (Os)
open XX (ad4)
open scoped Polynomial nonZeroDivisors RatFunc
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
attribute [local instance] Polynomial.algebra
private theorem gDC {t:F} (ht:znN k t) :
    let:=Os k (F:=F)
    znN (ziC k) (ztW t) := by
  let:=Os k (F:=F)
  let j:=z12 k[X][X] (ziC k)[X]
  let f :=(zEU (R:=ziC k) (ztW t)).toRingHom
  let g:=(z12 F[X] (ziC F)).comp
    ((zhd (zEU (R:=k) t).toRingHom).comp
      (zwz (R:=k)).toRingHom)
  have hfg:f.comp j=g:= by
    apply z86
    · intro q
      simp only [zQb,f,g,j,zeg,
        zKC,zrL]
      change zEU (R:=ziC k) (ztW t)
        (z1z (z12 k[X] (ziC k) q)) =
        z12 F[X] (ziC F)
          ((zwz (z1z q)).map
            (zEU (R:=k) t).toRingHom)
      rw [z8q,ad4,Polynomial.Bivariate.swap_C,
        zoi]
      have hmap : (zEU (R:=k) t).toRingHom.comp z1z =
          algebraMap k F:= by
        apply zz5
        intro a
        exact z8q t a
      rw [hmap]
    · simp only [zQb,f,g,j,zeg,
        zKC,zSo]
      change zEU (R:=ziC k) (ztW t) z7y =
        z12 F[X] (ziC F)
          ((zwz (z7y:k[X][X])).map
            (zEU (R:=k) t).toRingHom)
      rw [Polynomial.Bivariate.swap_Y,zrL]
      simp
  have hg:zq4 g :=
    (RatFunc.algebraMap_injective F).comp
      ((zTo _ (transcendental_iff_injective.mp ht)).comp
        (zwz (R:=k)).injective)
  let M:=(k[X]⁰).map (z1z:k[X] →+* k[X][X]).toMonoidHom
  let:zNo M (ziC k)[X] :=zyz _ _
  apply transcendental_iff.mpr
  intro p hp
  obtain ⟨⟨q,d⟩,hd⟩:=zg4 M p
  change p*j (d:k[X][X])=j q at hd
  have hz :g q=0:= by
    rw [← hfg]
    change f (j q)=0
    change f p=0 at hp
    rw [← hd,zok,hp,z1S]
  have hq:q=0:=hg (hz.trans (zhc g).symm)
  rw [hq,zhc] at hd
  exact (mul_eq_zero.mp hd).resolve_right (z0j (ziC k)[X] d).ne_zero
private def cHY {L:Type} [zrb L] [zZE L F]
   (S:Subfield (ziC F)) (h : ∀ a :L,ztW (z12 L F a)∈S) :
   IntermediateField L F :=
 (S.comap (ztW:F →+* ziC F)).toIntermediateField
   (fun a=>Subfield.mem_comap.mpr (h a))
private theorem bgs (S:Subfield (ziC F))
   (hC : ∀ a :F,ztW a∈S) (hX:zyX∈S) (z :ziC F) :
   z∈S:= by
 have hpoly (p:F[X]) :z12 F[X] (ziC F) p∈S:= by
   induction p using zCU with
   | add p q hp hq=>exact map_add (algebraMap F[X] (RatFunc F)) p q ▸ S.add_mem hp hq
   | monomial n a =>
     rw [RatFunc.algebraMap_monomial]
     exact S.mul_mem (hC a) (S.pow_mem hX _)
 induction z using zSH with
 | f p q _=>exact S.div_mem (hpoly p) (hpoly q)
theorem proof :XX.c3:= by
  intro k F _ _ _ t ht
  let:=Os k (F:=F)
  let E :=zvb k ({t} : Set F)
  let D:=zvb (ziC k) ({ztW t} : Set (ziC F))
  let:zQO E F:=ht.2.1
  let:zw7 E F:=ht.2.2
  have hconst (a :k) :ztW (z12 k F a)∈D:= by
    have h:=D.algebraMap_mem (ztW a)
    rw [← zyJ,ad4,zrL,
      zyJ] at h
    exact h
  have hX:zyX∈D:= by
    have h:=D.algebraMap_mem (zyX:ziC k)
    rw [← zYR,ad4,zSo,
      zYR] at h
    exact h
  have hE (a :E) :ztW (a :F)∈D:= by
    let S:=cHY D.toSubfield hconst
    have hle :E≤S:=IntermediateField.adjoin_simple_le_iff.mpr
      (zmq _ _ (zT1 _))
    exact hle a.property
  let i:E →+* D:=(RatFunc.C.comp (z12 E F)).codRestrict D.toSubring hE
  obtain ⟨a,ha⟩:=Field.exists_primitive_element E F
  let B:=zvb D ({ztW a} : Set (ziC F))
  have hgen:B = ⊤ := by
    apply top_unique
    intro z _
    have hB (b:E) :ztW (z12 E F b)∈B :=
      B.algebraMap_mem (⟨_,hE b⟩:D)
    let S:=cHY B.toSubfield hB
    have hle :zvb E ({a} : Set F)≤S :=
      IntermediateField.adjoin_simple_le_iff.mpr
        (zmq _ _ (zT1 _))
    have hC (b:F) :ztW b∈B:= by
      apply hle
      rw [ha]
      exact IntermediateField.mem_top
    exact bgs B.toSubfield hC (B.algebraMap_mem (⟨_,hX⟩:D)) z
  have hsep:IsSeparable D (ztW a) := by
    have ha_sep: (minpoly E a).Separable :=zMb E a
    refine ha_sep.map.of_dvd (minpoly.dvd D (ztW a) (p:=(minpoly E a).map i) ?_)
    have hmap : (z12 D (ziC F)).comp i=RatFunc.C.comp (z12 E F) :=rfl
    have heval :=Polynomial.map_aeval_eq_aeval_map hmap (minpoly E a) a
    rw [minpoly.aeval,zhc] at heval
    exact heval.symm
  let equiv :B ≃ₐ[D] ziC F :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  refine ⟨gDC ht.1,?_,?_⟩
  · let:zQO D B:=IntermediateField.adjoin.finiteDimensional hsep.isIntegral
    exact equiv.toLinearEquiv.finiteDimensional
  · let:zw7 D B:= by
      apply (IntermediateField.isSeparable_adjoin_iff_isSeparable D (ziC F)).mpr
      simpa using hsep
    exact AlgEquiv.Algebra.isSeparable equiv
end
end czD
end
section
namespace dng
noncomputable section
open aR dN vS B8
open scoped Polynomial TensorProduct
private def a3X:g9 ≃+* zlg[X] :=
 ((zGY zA7 zOE).trans
   (MvPolynomial.optionEquivLeft zA7 (Fin 4))).toRingEquiv
private theorem cRW :
   a3X.toRingHom.comp qK=Polynomial.C:= by
 apply zXT
 · intro a
   simp [a3X,qK,MvPolynomial.optionEquivLeft_C]
 · intro i
   simp [a3X,qK,MvPolynomial.optionEquivLeft_X_some]
@[simp] private theorem cRX (D:zlg) :
   a3X (qK D)=z1z D :=
  zmU cRW D
private theorem eyX (P:znc zlg) :
  (zr0 P).map (a3X:g9 →+* zlg[X])=P.map Polynomial.C:= by
 rw [← RingEquiv.toRingHom_eq_coe,zr0,z0L,cRW]
private def a3i (P:znc zlg) :
   (g9 ⧸ zr0 P) ≃+* (zlg ⧸ P)[X] :=
 (Ideal.quotientEquiv (zr0 P) (P.map z1z) a3X (eyX P).symm).trans
   P.polynomialQuotientEquivQuotientPolynomial.symm
@[simp] private theorem cJg (P:znc zlg) (D:zlg) :
    a3i P (zVv (zr0 P) (qK D)) =
      z1z (zVv P D) := by
  rw [a3i,RingEquiv.trans_apply,Ideal.quotientEquiv_mk,cRX,
    Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk,zrL]
private theorem cJk {P:znc zlg} {D:zlg}
  (h:zWc (zVv P D)) :
  zWc (zVv (zr0 P) (qK D)) := by
 intro x y he
 apply (a3i P).injective
 have he' := zPw (a3i P) he
 simp only [zok,cJg] at he'
 ext n
 have hn:=zPw (fun p: (zlg ⧸ P)[X]=>p.coeff n) he'
 exact h (by simpa only [Polynomial.coeff_C_mul] using hn)
private theorem cZ3 {P:znc zlg} {D:zlg} :
  qK D∈zr0 P↔D∈P:= by
 rw [← z1Q,← (a3i P).map_eq_zero_iff,
  cJg,Polynomial.C_eq_zero,z1Q]
private theorem bZE {P:znc zlg} (hP:P.IsPrime) : (zr0 P).IsPrime := by
 let:=hP
 let h:ztn (g9 ⧸ zr0 P) :=
  MulEquiv.isDomain (zlg ⧸ P)[X] (a3i P).toMulEquiv
 exact (Ideal.Quotient.isDomain_iff_prime (zr0 P)).mp h
private theorem cJj {I P:znc zlg} (hP:I.IsMinimalPrime P) :
  (zr0 I).IsMinimalPrime (zr0 P) := by
 refine ⟨⟨bZE hP.isPrime,Ideal.map_mono hP.le⟩,?_⟩
 intro T hT hTP
 let:=hT.1
 have hle :T.comap qK≤P:= fun _ hx =>
  cZ3.mp (hTP hx)
 have hPT:P≤T.comap qK :=
  hP.2 ⟨zG1 _ _,Ideal.map_le_iff_le_comap.mp hT.2⟩ hle
 exact Ideal.map_le_iff_le_comap.mpr hPT
private theorem cJh {P:znc zlg}
  (h:zqg (zlg ⧸ P)=2) :TB (zr0 P) 3:= by
 unfold TB
 have he :zqg (g9 ⧸ zr0 P)=zqg ((zlg ⧸ P)[X]) :=
  ringKrullDim_eq_of_ringEquiv (a3i P)
 rw [he,Polynomial.ringKrullDim_of_isNoetherianRing,h]
 norm_num
private theorem c70 {F G:zlg} (hF:F≠0)
  (hG:zWc (zVv (zye {F}) G)) :
  IsRelPrime F G:= by
 rintro a ⟨b,hab⟩ ⟨c,hac⟩
 have hb:b≠0:=zJ0 (hab ▸ hF)
 have hmul :G*b∈(zye {F} : znc zlg) := by
  apply Ideal.mem_span_singleton.mpr
  exact ⟨c,by rw [hab,hac]; ring⟩
 have hz :zVv (zye {F}) b=0 :=
  (isLeftRegular_iff_right_eq_zero_of_mul.mp hG) _ (by
    rw [← zok]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmul)
 have hd:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 apply isUnit_iff_dvd_one.mpr
 apply (mul_dvd_mul_iff_left hb).mp
 simpa only [zqe,hab,zDE b a] using hd
local instance :zZE zlg g9:=qK.toAlgebra
local instance :Module.Flat zlg g9:= by
  let e :g9 ≃ₐ[zlg] zlg[X] :=
    { a3X with
      commutes' := by
        intro b
        exact cRX b }
  let:=Module.Free.of_basis (Polynomial.basisMonomials zlg)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv
private theorem cJi (I P:znc zlg) (hP:P.IsPrime) :
    oA I P hP=Ro (zr0 I) (zr0 P) (bZE hP) := by
  let:=hP
  let:=bZE hP
  let: (zr0 P).LiesOver P:=⟨by
    ext D
    exact cZ3.symm⟩
  let A:=zhy P
  let B:=zhy (zr0 P)
  let:zZE A B:=Localization.AtPrime.algebraOfLiesOver P (zr0 P)
  have :zsf zlg A B:=inferInstance
  have :IsLocalHom (z12 A B) := by
    rw [Localization.AtPrime.algebraMap_eq P (zr0 P)]
    infer_instance
  have hmap (L:znc zlg) :
      (L.map (z12 zlg A)).map (z12 A B) =
        (zr0 L).map (z12 g9 B) := by
    change (_:znc B)=(L.map (z12 zlg g9)).map (z12 g9 B)
    rw [z0L,z0L,← zYY,
      ← zYY]
  have hmax : (zrY A).map (z12 A B)=zrY B:= by
    rw [← zRt (I:=P),hmap,
      zRt]
  let L:=I.map (z12 zlg A)
  have hsimple :IsSimpleModule B (B ⧸ zrY B) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal B).1
  have hlen:=IsLocalRing.length_baseChange A B (A ⧸ L)
  rw [hmax,Module.length_eq_one B (B ⧸ zrY B),zqe] at hlen
  change Module.length A (A ⧸ L) =
    Module.length B (B ⧸ (zr0 I).map (z12 g9 B))
  rw [← hmap I]
  exact hlen.symm.trans (zeK B L).toLinearEquiv.length_eq.symm
end
end dng
end
section
namespace Jq
noncomputable section
open MvPolynomial
def previous (i:Fin 5) :Form →+* Form :=
 eval₂Hom C (fun j=>z9v j+C (if j=i then -1 else 0))
def auj (i:Fin 5) :Form →+ Form :=
 AddMonoidHom.id Form-(previous i).toAddMonoidHom
theorem bBr (i:Fin 5) (p:Form) :
 auj i p=p - previous i p:=rfl
theorem ccA (i:Fin 5) (p:Form) (t:jJ) :
    eval (fun j=>((t+zY i) j:ℚ)) (previous i p) =
      eval (fun j=>(t j:ℚ)) p:= by
  let R:=eval (fun j=>(t j:ℚ))
  let L:=(eval (fun j=>((t+zY i) j:ℚ))).comp (previous i)
  have h:L=R:= by
    ext j
    · simp [L,R,previous]
    · by_cases hij:i=j
      · subst j
        simp [L,R,previous,zY]
      · simp [L,R,previous,zY,zoV,hij,z9m hij]
  exact zmU h p
theorem bpq (i:Fin 5) {f g h:jJ→ℕ} {p q r :Form}
  (hp:zmV p (fun t=>f t)) (hq:zmV q (fun t=>g t))
  (hr :zmV r (fun t=>h t))
  (hex : ∀ t,f (t+zY i)+h t=g (t+zY i)) :
  p=q - previous i r := by
 obtain ⟨N,hN⟩:=hp
 obtain ⟨M,hM⟩:=hq
 obtain ⟨L,hL⟩:=hr
 refine cMw (N :=max (max N M) L+1) fun u hu => ?_
 have he (j:Fin 5) :zY i j≤1 := by
  simp only [zY,zoV]
  split <;> omega
 let t:jJ:=Finsupp.equivFunOnFinite.symm fun j=>u j - zY i j
 have hut:t+zY i=u:= by
  ext j
  have h:=hu j
  have h' := he j
  change u j - zY i j+zY i j=u j
  omega
 have hprev :eval (fun j=>(u j:ℚ)) (previous i r)=eval (fun j=>(t j:ℚ)) r := by
  rw [← hut,ccA]
 have hNu : ∀ j,N≤u j:= fun j=> by have :=hu j; omega
 have hMu : ∀ j,M≤u j:= fun j=> by have :=hu j; omega
 have hLt (j:Fin 5) :L≤t j:= by
  have h:=hu j
  have h' := he j
  change L≤u j - zY i j
  omega
 rw [zpO,hprev,hN _ hNu,hM _ hMu,hL _ hLt,eq_sub_iff_add_eq]
 change (f u:ℚ)+(h t:ℚ)=(g u:ℚ)
 exact_mod_cast (hut ▸ hex t)
private theorem eNT (i:Fin 5) (a :jJ) (r :ℚ) :
  previous i (ztt (a.erase i) r)=ztt (a.erase i) r := by
 rw [previous,eval₂Hom_monomial,monomial_eq]
 congr 1
 apply Finsupp.prod_congr
 intro j hj
 have hij:j≠i:= fun h=>(Finsupp.mem_support_iff.mp hj) (by simp [h])
 simp [hij]
private theorem gqr (i:Fin 5) (a :jJ) (r :ℚ) :
    previous i (ztt a r) =
      ∑ k∈z4x (a i+1),
        ztt (a.erase i+Finsupp.single i k)
          (r*((-1 :ℚ)^(a i - k)*((a i).choose k :ℚ))) := by
  have hm:ztt a r=z9v i^a i*ztt (a.erase i) r := by
    conv_lhs=>rw [← zop i a,zV6]
    exact monomial_single_add
  rw [hm,zok,zkq,eNT]
  have hx :previous i (z9v i)=z9v i+C (-1) := by simp [previous]
  rw [hx,add_pow,zkr]
  refine zUo rfl fun k _ => ?_
  rw [← zkq,← zGu (znf:ℚ →+* Form) ((a i).choose k)]
  calc
    _=(C ((-1 :ℚ)^(a i - k))*C ((a i).choose k :ℚ)) *
        (z9v i^k*ztt (a.erase i) r) := by ring
    _ = _:= by
      rw [← zok,← monomial_single_add,C_mul_monomial,
        zV6 (zhf i k) (a.erase i),zDE _ r]
private theorem cCK (i:Fin 5) (a :jJ) (r :ℚ) :
    auj i (ztt a r) =
      ∑ k∈z4x (a i),
        ztt (a.erase i+Finsupp.single i k)
          (-(r*((-1 :ℚ)^(a i - k)*((a i).choose k :ℚ)))) := by
  rw [bBr,gqr,zpB]
  simp [zop,← Finset.sum_neg_distrib]
private theorem cMC (i:Fin 5) (a :jJ) :
  (a.erase i).degree+a i=a.degree := by
 simpa using zPw Finsupp.degree (zop i a)
theorem cCI (i:Fin 5) {p:Form} (a :jJ)
  (h:p.totalDegree≤a.degree) : (auj i p).coeff a=0:= by
 classical
 rw [← p.support_sum_monomial_coeff,zdo,zqN]
 refine zYF fun b hb => ?_
 have hb' : b.degree≤a.degree :=(le_totalDegree hb).trans h
 rw [cCK,zqN]
 refine zYF fun k hk => ?_
 apply zdp
 have hd:=cMC i b
 have hk' := Finset.mem_range.mp hk
 have hb'' : (b.erase i+Finsupp.single i k).degree<a.degree := by
  rw [zrl,Finsupp.degree_single]
  omega
 exact (totalDegree_monomial_le _ _).trans_lt hb''
theorem blI (i:Fin 5) {p:Form} {d:ℕ}
  (h:p.totalDegree≤d+1) : (auj i p).totalDegree≤d:= by
 refine zf9 fun a ha => ?_
 by_contra! hda
 exact (mem_support_iff.mp ha) (cCI i a (h.trans hda))
theorem bKH (i:Fin 5) {p:Form} (a :jJ)
  (h:p.totalDegree≤a.degree) : (previous i p).coeff a=p.coeff a := by
 have hz :=cCI i a h
 rw [bBr,coeff_sub] at hz
 exact (sub_eq_zero.mp hz).symm
theorem ccz (i:Fin 5) {p:Form} {d:ℕ}
  (h:p.totalDegree≤d) : (previous i p).totalDegree≤d:= by
 refine zf9 fun a ha => ?_
 by_contra! hda
 have h' := h.trans hda.le
 exact (mem_support_iff.mp ha)
  ((bKH i a h').trans (zdp (h.trans_lt hda)))
private theorem dxV (i:Fin 5) {a b:jJ}
   (ha :a i=0) (hb:b.degree≤a.degree+1) (r :ℚ) :
   (auj i (ztt b r)).coeff a=(ztt b r).coeff (a+zY i) := by
 classical
 rw [cCK,zqN]
 by_cases he :b=a+zY i
 · subst b
   have hv : (a+zY i) i=1 := by simp [zY,ha]
   have herr : (a+zY i).erase i+Finsupp.single i 0=a := by
     ext j
     by_cases hj:j=i <;> simp [zY,hj,ha]
   rw [hv,Finset.sum_range_one,herr]
   norm_num
 · rw [z0I,zNB he]
   refine zYF fun k hk => ?_
   rw [z0I,zNB]
   intro heq
   have hk0:k=0:= by
     have hp:=zPw (fun t:jJ=>t i) heq
     simpa [ha] using hp
   subst k
   have heq' : a=b.erase i:= by simpa using heq.symm
   have hd:=cMC i b
   have hk' := Finset.mem_range.mp hk
   rw [← heq'] at hd
   have hb' : b i=1 := by omega
   exact he (by rw [heq',zY,← hb',zop])
theorem blH (i:Fin 5) {I:zJe (Fin 5)} (hi:i∉I)
  {p:Form} (h:p.totalDegree≤I.card+1) :
  (auj i p).coeff (zu2 I)=p.coeff (zu2 (insert i I)) := by
 have ha :zu2 I i=0:= by simp [bOn,hi]
 rw [guw hi,← p.support_sum_monomial_coeff,zdo,zqN,zqN]
 refine zUo rfl fun b hb => ?_
 exact dxV i ha
  (by rw [aJC]; exact (le_totalDegree hb).trans h) (p.coeff b)
end
end Jq
end
section
namespace aA8
noncomputable section
open dN XT MvPolynomial
open Jq (jJ Form aJC OQ zY ccA auj bBr blI blH)
private theorem eiR (b:ℕ) (w:GG) (i:Fin 4) :
   cV b (w+Pi.single i 1)=cV b w+zY i.castSucc:= by
 ext j
 refine Fin.lastCases ?_ (fun k => ?_) j
 · rw [zSs,bHv,bHv,zY,
     Finsupp.single_eq_of_ne' (Fin.castSucc_ne_last i),z0a]
 · by_cases h:i=k
   · subst k
     simp [zY]
   · simp [zY,z9m h]
private theorem cWL {N :ℕ} {w:GG} (hw : ∀ j,N≤w j)
  (i:Fin 4) (s :ℕ) : ∀ j,N≤(w+Pi.single i s :GG) j :=
 fun j=>(hw j).trans (Nat.le_add_right _ _)
private theorem gGY (b N :ℕ) (dirs :List (Fin 4))
    (H :GG→ℝ) (p:Form) (u:jJ)
    (h : ∀ w,(∀ j,N≤w j) →
      H w=(eval (fun j=>((cV b w+u) j:ℚ)) p:ℝ)) :
    ∃ v :jJ,∀ w,(∀ j,N≤w j) →
      afK dirs 1 H w=(eval (fun j=>((cV b w+v) j:ℚ))
        ((dirs.map Fin.castSucc).foldl (fun q j=>auj j q) p) :ℝ) := by
  induction dirs generalizing H p u with
  | nil=>exact ⟨u,h⟩
  | cons i dirs ih =>
    simp only [afK,List.foldl_cons,List.map_cons]
    apply ih (ZH H i 1) (auj i.castSucc p) (u+zY i.castSucc)
    intro w hw
    have hs :cV b (w+Pi.single i 1)+u=(cV b w+u)+zY i.castSucc:= by
      rw [eiR]
      abel
    have hu:cV b w+(u+zY i.castSucc) =
        (cV b w+u)+zY i.castSucc:=(zd8 _ _ _).symm
    rw [ZH,h _ (cWL hw i 1),h _ hw,hs,hu,
      bBr,zpO,Rat.cast_sub,ccA]
private theorem edn (dirs :List (Fin 5)) (hn:dirs.Nodup)
   (p:Form) (hp:p.totalDegree≤dirs.length) :
   dirs.foldl (fun q j=>auj j q) p=C (p.coeff (zu2 dirs.toFinset)) := by
 induction dirs generalizing p with
 | nil =>
   have hz :p.totalDegree=0:=za7 hp
   simpa only [List.foldl_nil,List.toFinset_nil,zu2,Finset.sum_empty] using
     (totalDegree_eq_zero_iff_eq_C.mp hz)
 | cons i dirs ih =>
   have hd:=(List.nodup_cons.mp hn)
   have hp' : p.totalDegree≤dirs.toFinset.card+1 := by
     rw [zi0 hd.2]
     exact hp
   have hnot:i∉dirs.toFinset := by simpa using hd.1
   rw [List.foldl_cons,ih hd.2 _ (blI i hp),
     blH i hnot hp',List.toFinset_cons]
private def vo (i:Fin 4) (s :ℕ) (H :GG→ℝ) (w:GG) :ℝ :=
 ∑ n∈z4x s,H (w+Pi.single i n)
private theorem dWW (F:GG→ℝ) (i j:Fin 4) (s t:ℕ) :
  ZH (vo i s F) j t=vo i s (ZH F j t) := by
 funext w
 simp only [ZH,vo,zQr]
 congr 1
 refine zUo rfl fun n _ => ?_
 congr 1
 abel
private theorem dWV (H :GG→ℝ) (i:Fin 4) (s :ℕ) :
   ZH H i s=vo i s (ZH H i 1) := by
 funext w
 induction s with
 | zero=>simp [ZH,vo]
 | succ s ih =>
   have hs : (w+Pi.single i s)+Pi.single i 1=w+Pi.single i (s+1) := by
    rw [zd8,← Pi.single_add]
   rw [vo,zpB]
   change ZH H i (s+1) w =
    vo i s (ZH H i 1) w+ZH H i 1 (w+Pi.single i s)
   rw [← ih]
   simp only [ZH,hs]
   ring
private theorem dWZ (dirs :List (Fin 4)) (F:GG→ℝ)
   (i:Fin 4) (s t:ℕ) :
   afK dirs t (vo i s F)=vo i s (afK dirs t F) := by
 induction dirs generalizing F with
 | nil=>rfl
 | cons j dirs ih =>
   change afK dirs t (ZH (vo i s F) j t) =
     vo i s (afK dirs t (ZH F j t))
   rw [dWW,ih]
private theorem gl5 (dirs :List (Fin 4)) (N s :ℕ) (F:GG→ℝ) (d:ℝ)
   (h : ∀ w,(∀ j,N≤w j)→afK dirs 1 F w=d)
   (w:GG) (hw : ∀ j,N≤w j) :
   afK dirs s F w=(s :ℝ)^dirs.length*d:= by
 induction dirs generalizing F w with
 | nil=>simpa [afK] using h w hw
 | cons i dirs ih =>
   change ∀ v,(∀ j,N≤v j) →
     afK dirs 1 (ZH F i 1) v=d at h
   change afK dirs s (ZH F i s) w =
     (s :ℝ)^(dirs.length+1)*d
   rw [dWV,dWZ]
   unfold vo
   rw [zUo rfl (fun n _=>ih (ZH F i 1) h _
     (cWL hw i n))]
   simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,zVI]
   ring
theorem eAW {A:Fin 4→Set Exponent} {B:Set Exponent} {P:znc zlg}
    {p:Form}
    (hp:zmV p (fun t=>(aH8 A B P (t 4) (fun i=>t i.castSucc) :ℚ)))
    (i:Fin 5) (hd:p.totalDegree≤4 - i.val) (hn:OQ p) :
    ∃ d:ℝ,0≤d∧aAV A B P i.val d:= by
  let dirs :=acC i.val
  let inds :=dirs.map Fin.castSucc
  let d:=p.coeff (zu2 inds.toFinset)
  have hdlen:dirs.length=4 - i.val := by simp [dirs,acC]
  have hnDirs :dirs.Nodup:=(List.nodup_finRange 4).sublist (List.drop_sublist _ _)
  have hnInds :inds.Nodup:=hnDirs.map (Fin.castSucc_injective 4)
  have hdInds :p.totalDegree≤ inds.length:= by simpa [inds,hdlen] using hd
  have hnonneg:0≤d:= by
    apply hn
    rw [aJC,zi0 hnInds]
    exact hdInds
  refine ⟨d,by exact_mod_cast hnonneg,?_⟩
  obtain ⟨N,hN⟩:=hp
  refine ⟨N,fun b w s hb hw => ?_⟩
  have he (v :GG) (hv : ∀ j,N≤v j) :
      lO A B P b v =
        (eval (fun j=>((cV b v+0) j:ℚ)) p:ℝ) := by
    have hlarge (j:Fin 5) :N≤ cV b v j:= by
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa using hb
      · simpa using hv k
    have h:=hN (cV b v) hlarge
    change eval (fun j=>(cV b v j:ℚ)) p =
      (aH8 A B P (cV b v (Fin.last 4)) (fun j=>cV b v j.castSucc) :ℚ) at h
    simpa only [z0a,bHv,eiK,Rat.cast_natCast,lO] using
      zPw (fun x :ℚ=>(x :ℝ)) h.symm
  obtain ⟨u,hu⟩:=gGY b N dirs (lO A B P b) p 0 he
  have hc (v :GG) (hv : ∀ j,N≤v j) :
      afK dirs 1 (lO A B P b) v=(d:ℝ) := by
    rw [hu v hv,edn inds hnInds p hdInds,eval_C]
  simpa only [hdlen] using gl5 dirs N s (lO A B P b) (d:ℝ) hc w hw
end
end aA8
end
section
namespace bRe
noncomputable section
open K1 aR jA Rk
open scoped Polynomial BigOperators
private def bLu {R:Type*} [za6 R] (z :R) (H res :R[X]) :
    mA→z3y (Fin 3) R[X] :=
  fun i=>i.elim (znf (z1z z)) (fun j =>
    znf (z75 j.val res) +
      ∑ k :Fin 3,if k.val≤j.val then
        znf (z75 (j.val - k.val) H)*z9v k
      else 0)
private def amA {R:Type*} [za6 R] (f :ao →+* R)
  (z :R) (H res :R[X]) :jK →+* z3y (Fin 3) R[X] :=
 MvPolynomial.eval₂Hom (MvPolynomial.C.comp (zhd f))
  (bLu z H res)
private theorem cZA {R S:Type*} [za6 R] [za6 S]
  (g:R →+* S) (f :ao →+* R) (z :R) (H res :R[X]) (F:jK) :
  zDK (zhd g) (amA f z H res F) =
    amA (g.comp f) (g z) (H.map g) (res.map g) F:= by
 have he : (zDK (zhd g)).comp (amA f z H res) =
    amA (g.comp f) (g z) (H.map g) (res.map g) := by
  apply zXT
  · intro p
    simp [amA,zoi]
  · intro i
    cases i <;> simp [amA,bLu,zvc,apply_ite]
 exact zmU he F
private theorem c8B (H res :ao[X]) (z :ao) (F:jK) :
  aPU H res z F=amA (zz4 ao) z H res F:= by
 have he : (az5 H res).comp (JX (z1z z)) =
    amA (zz4 ao) z H res := by
  apply zXT
  · intro p
    simp [amA,JX,az5]
  · intro i
    cases i <;> simp [amA,bLu,JX,az5,jet]
 exact zmU he F
private abbrev bjN (d:ao[X]) :=Localization.Away d
private abbrev pO (d:ao[X]) :ao[X] →+* bjN d:=z12 _ _
private def aih {S:Type*} [zrb S] {d:ao[X]} (g:ao[X] →+* S)
  (hg:g d≠0) :bjN d →+* S :=
 ztx d (isUnit_iff_ne_zero.mpr hg)
@[simp] private theorem dcO {S:Type*} [zrb S] {d:ao[X]}
   (g:ao[X] →+* S) (hg:g d≠0) :
   (aih g hg).comp (pO d)=g :=
  IsLocalization.Away.lift_comp d _
@[simp] private theorem co0 {S:Type*} [zrb S] {d:ao[X]}
   (g:ao[X] →+* S) (hg:g d≠0) (a :ao[X]) :
   aih g hg (pO d a)=g a :=
  IsLocalization.Away.lift_eq d _ a
private theorem goi {S:Type*} [zrb S] {d:ao[X]}
  (g:ao[X] →+* S) (hg:g d≠0) (hi:zq4 g) :
  zq4 (aih g hg) := by
 have hd:d≠0:= fun h=>hg (by simp [h])
 have ha :zq4 (pO d) :=
  IsLocalization.injective (bjN d) (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
 unfold aih ztx
 exact (IsLocalization.lift_injective_iff _).mpr fun x y=>ha.eq_iff.trans hi.eq_iff.symm
private def b77 (n:ao[X][X]) (d:ao[X]) : (bjN d)[X] :=
 z1z (zdx d)*n.map (pO d)
private theorem cZw {S:Type*} [zrb S] {d:ao[X]}
  (g:ao[X] →+* S) (hg:g d≠0) (n:ao[X][X]) :
  (b77 n d).map (aih g hg)=z1z ((g d)⁻¹)*n.map g:= by
 have h:=zPw (aih g hg) (IsLocalization.Away.mul_invSelf (S:=bjN d) d)
 change aih g hg (pO d d* zdx d)=aih g hg 1 at h
 rw [zok,zXs,co0] at h
 simp [b77,zoi,eq_inv_of_mul_eq_one_right h]
private theorem gt6 {Γ s} (P:jF Γ s) (L:kH P)
    (r :ℕ) (F:jK) (z :ao) (hz :L.denominator.eval z≠0)
    (hF: (znf (jH P.H))^r∣restore P L F) :
    znf (P.H^r) ∣
      aPU P.H (Tj L.numerator L.denominator z) z F:= by
  let d:=L.denominator
  let f :=(pO d).comp (z1z:ao →+* ao[X])
  let HH :=P.H.map f
  let D:=HH^r
  let A:=amA f (pO d z7y) HH (b77 L.numerator d) F
  let gf :ao[X] →+* kS:=z12 _ _
  let ev :=zhz z
  let hg:gf d≠0:= by
    intro h
    have hd:d=0 :=
      (zxb ao[X] kS) (h.trans (zhc _).symm)
    apply hz
    change d.eval z=0
    simp [hd]
  let he :ev d≠0:=hz
  let g:=aih gf hg
  let e :=aih ev he
  have hgf :g.comp f=z12 ao kS:= by
    dsimp only [g,f]
    rw [← zxS,dcO]
    exact (zYY ao ao[X] kS).symm
  have hef :e.comp f=zz4 ao:= by
    dsimp only [e,f]
    rw [← zxS,dcO]
    apply zz5
    intro c
    change (z1z c).eval z=c
    simp
  have hgH :HH.map g=jH P.H := by
    dsimp only [HH]
    rw [zoi,hgf,jA.jH]
  have heH :HH.map e=P.H := by
    dsimp only [HH]
    rw [zoi,hef,zeh]
  have hgA:zDK (zhd g) A=restore P L F:= by
    dsimp only [A]
    rw [cZA,hgf,hgH]
    dsimp only [g]
    rw [co0,cZw]
    rfl
  have heA:zDK (zhd e) A =
      aPU P.H (Tj L.numerator d z) z F:= by
    dsimp only [A]
    rw [cZA,hef,heH]
    dsimp only [e]
    rw [co0,cZw,c8B]
    simp [ev,Tj]
  have hD:D.Monic:=((P.monic.map f).pow r)
  have hgD:D.map g=(jH P.H)^r := by
    dsimp only [D]
    rw [z5m,hgH]
  have heD:D.map e=P.H^r := by
    dsimp only [D]
    rw [z5m,heH]
  have hdvd:znf D ∣A:= by
    apply (zXG _ _).mpr
    intro m
    have hm:=(zXG _ _).mp
      (show znf (D.map g) ∣
          zDK (zhd g) A by
        rw [hgA,hgD,zkq]
        exact hF) m
    rw [zS3] at hm
    apply (zNp hD).mp
    apply zTo g (goi gf hg (zxb _ _))
    rw [Polynomial.map_modByMonic g hD,zgY]
    exact (zNp (hD.map g)).mpr hm
  have h:=map_dvd (zDK (zhd e)) hdvd
  rw [zpw,heA] at h
  change znf (D.map e)∣ _ at h
  rwa [heD] at h
private def aWN (i:Fin 3) :ℕ:=131071 - i.val
private def bPl (h:ℕ) (i:mA) :ℕ :=
 i.elim 0 (fun j=>131071+h - j.val)
private theorem weight_eq_sum {σ:Type*} (m:σ →₀ ℕ) (w:σ→ℕ) :
  m.weight w=m.sum (fun i e=>w i*e) := by
 rw [zDM]
 congr 1
 funext i e
 exact z5A _ _
private theorem cfm {H res :ao[X]} (z :ao) {B:ℕ} {F:jK}
    (hres :res.natDegree≤H.natDegree) (hF:ahb H.natDegree B F) :
    aPU H res z F∈zgW aWN B:= by
  have hf :F∈zgW (bPl H.natDegree) B :=
    MvPolynomial.mem_restrictJointDegree.mpr fun m hm=> by
      have hw:m.weight (bPl H.natDegree) =
          m.sum (fun i e=>i.elim 0 (fun j=>(131071+H.natDegree - j.val)*e)) := by
        rw [weight_eq_sum]
        congr 1
        funext i e
        cases i <;> simp [bPl]
      rw [hw]
      exact hF m (MvPolynomial.mem_support_iff.mpr hm)
  have hv (i:mA) :
      bLu z H res i ∈
        zgW aWN (bPl H.natDegree i) := by
    cases i with
    | none =>
      exact z8b _ (by simp)
    | some j =>
      change _+_∈zgW aWN (131071+H.natDegree - j.val)
      apply zcy
      · apply z8b
        have hj:=j.isLt
        have hd:=zax res j.val
        omega
      · apply zo3
        intro k _
        by_cases hk :k.val≤j.val
        · rw [zYo hk]
          by_cases hd:j.val - k.val≤H.natDegree
          · apply MvPolynomial.restrictJointDegree_mono aWN _
              (MvPolynomial.mul_mem_restrictJointDegree
                (z8b aWN
                  (zax H (j.val - k.val)))
                (MvPolynomial.X_mem_restrictJointDegree aWN k zs0))
            have hj:=j.isLt
            have hk' := k.isLt
            unfold aWN
            omega
          · rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _ (Nat.lt_of_not_ge hd),
              zhc,z1S]
            exact z4M _
        · rw [zNB hk]
          exact z4M _
  rw [c8B,amA]
  have he : (MvPolynomial.C.comp (zhd (zz4 ao))) =
      (znf:ao[X] →+* af 3) := by
    apply zz5
    intro p
    change znf (p.map (zz4 ao))=znf p
    rw [zeh]
  rw [he,MvPolynomial.eval₂Hom_C_eq_bind₁]
  exact MvPolynomial.bind₁_mem_restrictJointDegree hv hf
theorem proof :Rk.c2 := by
 intro w Γ s P L box t F hF γ hγ
 let z :=P.z γ
 let res :=Tj L.numerator L.denominator z
 let r :=box.b+box.j
 obtain ⟨Q,hQ⟩:=gt6 P L r F z (L.regular γ hγ) hF.2.2.2
 refine ⟨Q,?_,hQ⟩
 have hres :res.natDegree≤P.H.natDegree := by
   unfold res Tj
   exact (Polynomial.natDegree_C_mul_le _ _).trans
     (Polynomial.natDegree_map_le.trans L.small.le)
 have hbound:=cfm z hres hF.2.1
 rw [hQ] at hbound
 intro m hm
 have hn:Q.coeff m≠0:=MvPolynomial.mem_support_iff.mp hm
 have hp: (P.H^r)≠0:=zm1 _ P.monic.ne_zero
 have hc: (znf (P.H^r)*Q).coeff m≠0:= by
   rw [z06]
   exact zBS hp hn
 have hb:=MvPolynomial.mem_restrictJointDegree.mp hbound m hc
 rw [z06,Polynomial.natDegree_mul hp hn,Polynomial.natDegree_pow] at hb
 simp only [weight_eq_sum,aWN] at hb
 change _≤t+r*P.H.natDegree at hb
 omega
end
end bRe
end
section
set_option maxSynthPendingDepth 8
namespace baB
noncomputable section
open gT aeF
open Polynomial
open scoped nonZeroDivisors IntermediateField.algebraAdjoinAdjoin
private theorem cMY {K E :Type} [zrb K] [zrb E] [zZE K E] (z :E) :
   letI:zZE K[X] E :=(zEU z :K[X] →ₐ[K] E).toRingHom.toAlgebra
   zsE K[X] E=FZ K z := by
 classical
 let:zZE K[X] E :=(zEU z :K[X] →ₐ[K] E).toRingHom.toAlgebra
 unfold FZ
 split_ifs with hz
 · apply Module.finrank_eq_zero_of_not_faithfulSMul
   exact fun hf=>(isAlgebraic_iff_not_injective.mp hz)
     ((zSO K[X] E).mp hf)
 · let B:=zvb K ({z} : Set E)
   let U:=Algebra.adjoin K ({z} : Set E)
   have ht:znN K z :=hz
   let e :=zjm K z ht
   let:zZE K[X] B:=((z12 U B).comp e.toRingHom).toAlgebra
   let:z0o K[X] B:=IsFractionRing.of_ringEquiv_left e.toRingEquiv fun _=>rfl
   let:zsf K[X] B E :=zsL fun p=> by
     change zEU z p=(zjm K z ht p:E)
     rw [Polynomial.algEquivOfTranscendental_apply,aeval_subalgebra_coe]
   exact (IsFractionRing.finrank_right_eq K[X] B E).symm
private def aj0 (A F:Type) [za6 A] [zrb F] [zZE A F] :
   A[X] →+* ziC F :=
 (z12 F[X] (ziC F)).comp (zhd (z12 A F))
@[simp] private theorem c4G {A F:Type} [za6 A] [zrb F] [zZE A F] (a :A) :
   aj0 A F (C a)=ztW (z12 A F a) := by simp [aj0]
@[simp] private theorem c4H (A F:Type) [za6 A] [zrb F] [zZE A F] :
   aj0 A F z7y=RatFunc.X:= by simp [aj0]
private theorem c4I (A F:Type) [za6 A] [ztn A]
   [zrb F] [zZE A F] [z0o A F] :
   letI:zZE A[X] (ziC F) :=(aj0 A F).toAlgebra
   z0o A[X] (ziC F) := by
 let:zZE A[X] (ziC F) :=(aj0 A F).toAlgebra
 let:FaithfulSMul A[X] (ziC F) :=(zSO ..).mpr <|
   (zxb F[X] (ziC F)).comp
     (zTo _ (zxb A F))
 apply z6t
 let M:zdT A[X] :=A⁰.map z1z
 let:zZE A[X] F[X] :=z87 A F
 let:zNo M F[X] :=zyz A⁰ F
 let j:=z12 F[X] (ziC F)
 intro z
 obtain ⟨r,s,-,hz⟩:=zJC F[X] z
 obtain ⟨a,b,d,ha,hb⟩:=IsLocalization.surj₂ M F[X] r s
 let t:=z12 A[X] F[X] (d:A[X])
 have ht:j t≠0:=((z0j F[X] d).map j).ne_zero
 have ha' : j r*j t=aj0 A F a := by
   rw [← zok]
   exact zPw j ha
 have hb' : j s*j t=aj0 A F b:= by
   rw [← zok]
   exact zPw j hb
 change ∃ a b,z=aj0 A F a/aj0 A F b
 exact ⟨a,b,by rw [← ha',← hb',mul_div_mul_right _ _ ht,hz]⟩
private def nested (k :Type) [zrb k] :zG0 k ≃+* zM1 (zM1 k) :=
 (z8s k 1).toRingEquiv.trans
   (Polynomial.mapEquiv (zpe k (Fin 1)).toRingEquiv)
@[simp] private theorem gRh {k :Type} [zrb k] (c:k) :
   nested k (znf c)=C (C c) := by
  simp [nested,MvPolynomial.finSuccEquiv_apply,MvPolynomial.uniqueAlgEquiv_apply]
@[simp] private theorem gRi {k :Type} [zrb k] :
   nested k (z9v 0)=z7y (R:=zM1 k) := by
  change zGG _ (z8s k 1 (z9v 0))= _
  rw [MvPolynomial.finSuccEquiv_X_zero,zSo]
@[simp] private theorem gRj {k :Type} [zrb k] :
   nested k (z9v 1)=C (z7y (R:=k)) := by
  let e :=zpe k (Fin 1)
  change zGG e.toRingHom
   (z8s k 1 (z9v (0:Fin 1).succ))= _
  rw [MvPolynomial.finSuccEquiv_X_succ,zrL]
  apply zPw C
  change zSZ z1z (fun _:Fin 1=>z7y) (z9v 0)= _
  rw [MvPolynomial.eval₂_X]
private def aIa (k :Type) [zrb k] :zG0 k ≃+* zM1 (zM1 k) :=
 (zGY k (Equiv.swap (0:Fin 2) 1)).toRingEquiv.trans (nested k)
@[simp] private theorem eoL {k :Type} [zrb k] (c:k) :
   aIa k (znf c)=C (C c) := by simp [aIa]
@[simp] private theorem eoM {k :Type} [zrb k] :
   aIa k (z9v 0)=C (z7y (R:=k)) := by simp [aIa]
@[simp] private theorem gQb {k :Type} [zrb k] :
   aIa k (z9v 1)=z7y (R:=zM1 k) := by simp [aIa]
private theorem ad4 {k F:Type} [zrb k] [zrb F] [zZE k F]
   (p:k[X]) :
   letI:=Os k (F:=F)
   z12 (ziC k) (ziC F) (z12 k[X] (ziC k) p) =
     aj0 k F p:= by
 let:zZE (ziC k) (ziC F) :=Os k
 change RatFunc.mapRingHom _ _ (z12 k[X] (ziC k) p)= _
 simp only [aj0,zQb,RatFunc.coe_mapRingHom_eq_coe_map]
 simpa using RatFunc.map_apply_div (zhd (z12 k F))
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
     (zTo _ (z12 k F).injective)) p 1
variable {k :Type} [zrb k] (H :znc (Ambient k)) [H.IsPrime]
theorem eKX (g h:Ambient k) :
    cbk H g h =
      ajJ k (zLN (zVv H g))
        (zLN (zVv H h)) := by
  let A:=gk H
  let F:=zNv A
  let L:=ziC F
  let R:=zG0 k
  let T:=zM1 (zM1 k)
  let S:=(ziC k)[X]
  let D:=A[X]
  let J:=aj0 A F
  let aRD:zZE R D:=(pD H g h).toAlgebra
  let:Module R D:=aRD.toModule
  let:SMul R D:=aRD.toSMul
  let aDL:zZE D L:=J.toAlgebra
  let:SMul D L:=aDL.toSMul
  let:z0o D L:=c4I A F
  let aRL:zZE R L:=(J.comp (pD H g h)).toAlgebra
  let:SMul R L:=aRL.toSMul
  let:Module R L:=aRL.toModule
  let:zsf R D L:=zsL fun _=>rfl
  change zsE R D = _
  rw [z4U (S:=D) R L]
  let:zZE (ziC k) L:=Os k
  let z :=J (Yn H g h)
  have hz :z=z12 F L (zLN (zVv H g)) +
      zyX*z12 F L (zLN (zVv H h)) := by
    change J (Yn H g h)=ztW (z12 A F (zVv H g)) +
      zyX*ztW (z12 A F (zVv H h))
    simp only [J,Yn,zrl,zok,c4G,c4H]
  rw [ajJ,← hz,← cMY z]
  let aSL:zZE S L:=(zEU z :S →ₐ[ziC k] L).toRingHom.toAlgebra
  let:SMul S L:=aSL.toSMul
  let aTS:zZE T S:=z87 k[X] (ziC k)
  let:SMul T S:=aTS.toSMul
  let aTL:zZE T L:=((z12 S L).comp (z12 T S)).toAlgebra
  let:SMul T L:=aTL.toSMul
  let:zsf T S L:=zsL fun _=>rfl
  let M:zdT T:=k[X]⁰.map z1z
  let:zNo M S:=zyz k[X]⁰ (ziC k)
  have hm:M≤T⁰:=map_le_nonZeroDivisors_of_injective z1z Polynomial.C_injective zs0
  rw [IsLocalization.finrank_eq S M hm]
  apply znv (aIa k) (RingEquiv.refl L)
  apply zXT
  · intro c
    change zEU z ((aIa k (znf c)).map (z12 k[X] (ziC k))) =
      J (pD H g h (znf c))
    simp only [eoL,zrL,z8q,ad4,
      btq,J,c4G]
    exact zPw (ztW (K:=F)) (zG3 k A F c)
  · intro i
    fin_cases i
    · change zEU z ((aIa k (z9v 0)).map
          (z12 k[X] (ziC k)))=J (pD H g h (z9v 0))
      simp only [eoM,zrL,z8q,ad4,
        cbh,J,c4H]
    · change zEU z ((aIa k (z9v 1)).map
          (z12 k[X] (ziC k)))=J (pD H g h (z9v 1))
      simp [z]
theorem gLa (g:Ambient k) :
    cbk H g 0 =
      FZ k (zLN (zVv H g)) := by
  let A:=gk H
  let F:=zNv A
  let L:=ziC F
  let R:=zG0 k
  let T:=zM1 (zM1 k)
  let D:=A[X]
  let P:=F[X]
  let J:=aj0 A F
  let aRD:zZE R D:=(pD H g 0).toAlgebra
  let:Module R D:=aRD.toModule
  let:SMul R D:=aRD.toSMul
  let aDL:zZE D L:=J.toAlgebra
  let:SMul D L:=aDL.toSMul
  let:z0o D L:=c4I A F
  let aRL:zZE R L:=(J.comp (pD H g 0)).toAlgebra
  let:SMul R L:=aRL.toSMul
  let:Module R L:=aRL.toModule
  let:zsf R D L:=zsL fun _=>rfl
  let v :=zLN (zVv H g)
  let:zZE k[X] F:=(zEU v :k[X] →ₐ[k] F).toRingHom.toAlgebra
  let aTP:zZE T P:=z87 k[X] F
  let:Module T P:=aTP.toModule
  let:SMul T P:=aTP.toSMul
  let aTL:zZE T L:=((z12 P L).comp (z12 T P)).toAlgebra
  let:SMul T L:=aTL.toSMul
  let:zsf T P L:=zsL fun _=>rfl
  change zsE R D = _
  rw [z4U (S:=D) R L,← cMY v]
  calc
    zsE R L=zsE T L:= by
      apply znv (nested k) (RingEquiv.refl L)
      apply zXT
      · intro c
        change z12 P L ((nested k (znf c)).map (z12 k[X] F)) =
          J (pD H g 0 (znf c))
        simp [zy4,J,aj0]
        exact zPw (ztW (K:=F)) (zG3 k A F c)
      · intro i
        fin_cases i
        · change z12 P L ((nested k (z9v 0)).map (z12 k[X] F)) =
            J (pD H g 0 (z9v 0))
          simp [J,aj0]
          rfl
        · change z12 P L ((nested k (z9v 1)).map (z12 k[X] F)) =
            J (pD H g 0 (z9v 1))
          simp [zy4,J,aj0,Yn,v,zLN]
          rfl
    _=zsE T P:=(z4U (S:=P) T L).symm
    _=zsE k[X] F:=zPw Cardinal.toNat (rank_polynomial_polynomial k[X] F)
end
end baB
end
section
set_option backward.isDefEq.respectTransparency false
namespace baB
noncomputable section
open ac4 K1_14_2_2_7_3_3
theorem proof :K1_14_2_2_7_3_3.c2 := by
  intro k _ H _ _ _ _
  constructor
  · have hi:TY H (z9v 0) (z9v 1) =
        H.map (Cl k) ⊔ zye
          {z9v 0+MvPolynomial.C (arW k 0)*z9v 1 -
            znf (arW k 1)} := by
      simp only [TY,a3W,z7N]
    have h:=(cRS H (z9v 0) (z9v 1)).trans
      (eKX H (z9v 0) (z9v 1))
    rw [hi] at h
    exact h
  · have hi:TY H (z9v 3) 0 =
        H.map (Cl k) ⊔ zye
          {z9v 3-MvPolynomial.C (arW k 1)} := by
      simp only [TY,a3W,z7N,zhc,znR,z0a]
    have h:=(cRS H (z9v 3) 0).trans (gLa H (z9v 3))
    rw [hi] at h
    exact h
end
end baB
end
section
namespace bz3
noncomputable section
open K1 aR cu gT Polynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private def aV7:z3y (Fin 2) FX ≃ₐ[FX] tK :=
 (Mt FX).trans (Polynomial.mapAlgEquiv (zpe FX (Fin 1)))
private theorem eFM (q:z3y (Fin 2) FX) (m:Fin 2 →₀ ℕ) :
    (((aV7 q).coeff (m 1)).coeff (m 0))=q.coeff m:= by
  change ((zGG (zpe FX (Fin 1)).toRingHom
    (Mt FX q)).coeff (m 1)).coeff (m 0)= _
  rw [Polynomial.coeff_map]
  change (zpe FX (Fin 1) ((Mt FX q).coeff (m 1))).coeff
    (m 0)= _
  rw [MvPolynomial.coeff_uniqueAlgEquiv,Mt,
    zfq,zyk,MvPolynomial.optionEquivLeft_coeff_coeff]
  have hm: (zhf (default :Fin 1) (m 0)).optionElim (m 1) =
      m.mapDomain finSuccEquivLast:= by
    ext o
    cases o with
    | none =>
      rw [Finsupp.optionElim_apply_none,
        ← show zOE (1 :Fin 2)=none from finSuccEquivLast_last,
        zm3 finSuccEquivLast.injective]
    | some i =>
      have hi:i=default :=Subsingleton.elim _ _
      subst i
      rw [Finsupp.optionElim_apply_some,Finsupp.single_eq_same,
        ← finSuccEquivLast_castSucc (default :Fin 1),
        zm3 finSuccEquivLast.injective]
      rfl
  rw [hm,MvPolynomial.coeff_rename_mapDomain _ finSuccEquivLast.injective]
private theorem eFN (q:z3y (Fin 2) FX) (S:K[X]) :
   FW (aV7 q) S=zY9 ![kr S,kr S.derivative] q:= by
 have h:=MvPolynomial.optionEquivLeft_elim_eval FX (Fin 1) (fun _:Fin 1=>kr S) (kr S.derivative)
   (MvPolynomial.rename zOE q)
 rw [MvPolynomial.eval_rename] at h
 have hvec: (fun o:zNO (Fin 1)=>o.elim (kr S.derivative) (fun _=>kr S)) ∘
     zOE = ![kr S,kr S.derivative] := by
   funext i
   fin_cases i <;> rfl
 rw [hvec] at h
 rw [FW,Polynomial.eval₂_eq_eval_map]
 change ((zGG (zhz (kr S))
   (zGG (zpe FX (Fin 1)).toRingHom (Mt FX q))).eval
     (kr S.derivative))= _
 have hcomp: (zhz (kr S)).comp
     (zpe FX (Fin 1)).toRingHom =
     zY9 (fun _:Fin 1=>kr S) := by
   apply zz5
   intro f
   change (zpe FX (Fin 1) f).eval (kr S) =
     zY9 (fun _:Fin 1=>kr S) f
   simpa only [Polynomial.eval₂_id,MvPolynomial.eval₂_id] using
     (MvPolynomial.eval₂_const_uniqueAlgEquiv (f :=f) (φ:=zz4 FX) (a :=kr S))
 rw [zoi,hcomp]
 exact h.symm
private theorem eval_lift (q:af 2) (S:K[X]) :
   zY9 ![kr S,kr S.derivative] (zDK
     (z12 ao[X] FX) q)=z12 ao[X] FX (cK q (extend S)) := by
 have h : ![kr S,kr S.derivative]=z12 ao[X] FX ∘ jet (extend S) := by
   funext i
   fin_cases i
   · simp [kr,j9,jet]
   · simp [kr,j9,jet,Polynomial.derivative_map]
 rw [h,cK,MvPolynomial.map_eval]
theorem cFG (G:tK) {B J:ℕ} (hG:G≠0) (hJ:G.natDegree≤J)
   (hB : ∀ j i,(G.coeff j).coeff i≠0→i+j≤B) :
   ∃ q:af 2,q≠0∧q.totalDegree≤B∧q.degreeOf 1≤J ∧
     ∀ S:K[X],FW G S=0→cK q (extend S)=0:= by
 classical
 let f :=aV7.symm G
 let D:=(ao[X]⁰).map (znf (σ:=Fin 2))
 obtain ⟨⟨q,d⟩,he⟩:=zg4 D f
 obtain ⟨a,ha,hd⟩:=d.property
 have hmap :f*znf (z12 ao[X] FX a) =
     zDK (z12 ao[X] FX) q:= by
   change f*zDK (z12 ao[X] FX) (d:af 2) =
     zDK (z12 ao[X] FX) q at he
   rwa [← hd,zpw] at he
 have hinj:zq4 (z12 ao[X] FX) :=zxb _ _
 have hne :f≠0:=(zw1 _ aV7.symm.injective).mpr hG
 have haq:z12 ao[X] FX a≠0:=(zw1 _ hinj).mpr (nonZeroDivisors.ne_zero ha)
 have hq:q≠0:= by
   intro hz
   exact zBS hne ((zw1 _ (MvPolynomial.C_injective (Fin 2) FX)).mpr haq)
     (by simpa only [hz,zhc] using hmap)
 have hc (m:Fin 2 →₀ ℕ) (hm:m∈q.support) : (G.coeff (m 1)).coeff (m 0)≠0:= by
   have hh:=zPw (fun z :z3y (Fin 2) FX=>z.coeff m) hmap
   rw [zDE f,z06,zS3,← eFM,
     show aV7 f=G from aV7.apply_symm_apply G] at hh
   intro hz
   exact (zw1 _ hinj).mpr (MvPolynomial.mem_support_iff.mp hm)
     (by simpa only [hz,znR] using hh.symm)
 refine ⟨q,hq,?_,?_,?_⟩
 · rw [MvPolynomial.totalDegree]
   apply zf9
   intro m hm
   change m.sum (fun _ n=>n)≤B
   rw [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_two]
   exact hB _ _ (hc m hm)
 · rw [MvPolynomial.degreeOf_eq_sup]
   apply zf9
   intro m hm
   refine le_trans ?_ hJ
   by_contra! hgt
   exact hc m hm (by rw [zQl hgt,zO6])
 · intro S hS
   have h:=zPw (zY9 ![kr S,kr S.derivative]) hmap
   rw [eval_lift,zok,← eFN,show aV7 f=G from aV7.apply_symm_apply G,
     hS,z1S] at h
   exact hinj (h.symm.trans (zhc _).symm)
end
end bz3
end
section
namespace WI
noncomputable section
open dN rW MvPolynomial Filter
open scoped BigOperators
private theorem bqT (I:n8) (g:zlg) (N :ℕ) (hN :g.totalDegree≤N) :
    ztr (I ⊔ zye {g}) N +
      ztr (I.colon {g}) (N - g.totalDegree)≤ztr I N := by
  let J:n8:=I ⊔ zye {g}
  let A:n8:=I.colon {g}
  let q:=z5F zA7 (show I≤J from zPQ)
  let cut:z9e I N →ₗ[zA7] z9e J N :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
      change q y.val∈_
      rw [← hpy]
      exact ziU hp
  have hcut:zpX cut:= by
    intro y
    obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
    exact ⟨⟨zVv I p,ziU hp⟩,zkt hpy⟩
  let mul :=(Vp I g).restrictScalars zA7
  let emb:z9e A (N - g.totalDegree) →ₗ[zA7] z9e I N :=
    (mul.domRestrict _).codRestrict _ fun y=> by
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
      change Vp I g y.val∈_
      rw [← hpy,azY]
      exact ziU ((zhM p g).trans (by omega))
  have hemb (y :z9e A (N - g.totalDegree)) :emb y∈z83 cut:= by
    rw [zeS]
    apply zkt
    change q (Vp I g y.val)=0
    have hex :=(LinearMap.exact_iff.mp (a7c I g))
    have hm:Vp I g y.val ∈
        zWl (Vp I g) :=LinearMap.mem_range_self _ _
    rw [← hex] at hm
    exact hm
  have hinj:zq4 (emb.codRestrict (z83 cut) hemb) := by
    intro x y he
    exact zkt (aPy I g
      (zPw (fun z=>z.val.val) he))
  have hker :=zdv hinj
  have hrank :=cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcut,zl4] at hrank
  change ztr J N+affineHilbertFunction A (N - g.totalDegree)≤_
  unfold ztr
  omega
theorem cUM (I:n8) (g:zlg) (hI:zIT I≤2) :
   (zIU (I ⊔ zye {g})).coeff 2 +
     (zIU (I.colon {g})).coeff 2≤(zIU I).coeff 2 := by
 let J:n8:=I ⊔ zye {g}
 let A:n8:=I.colon {g}
 let b:=g.totalDegree
 let S:=zIU J+Polynomial.taylor (-(b:ℚ)) (zIU A)
 have hA:zIT A≤2 :=
   (zy5 Ideal.le_colon).trans hI
 have hJ:zIT J≤2 :=
   (zy5 zPQ).trans hI
 have hS:S.natDegree≤2 :=
   Polynomial.natDegree_add_le_of_degree_le hJ (by rwa [Polynomial.natDegree_taylor])
 have hc:S.coeff 2≤(zIU I).coeff 2 := by
   refine Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hS hI ?_
   obtain ⟨N₀,h₀⟩:=zQf A
   filter_upwards [zaL J,zaL I,
     eventually_ge_atTop (N₀+b)] with N h₁ h₂ hN
   have hb:b≤N := by omega
   simp only [S,zvF,Polynomial.taylor_eval,h₁,h₂,← sub_eq_add_neg,
     ← zjK hb,h₀ (N - b) (by omega :N₀≤N - b)]
   exact_mod_cast bqT I g N hb
 simpa only [S,z7l,Polynomial.coeff_taylor_of_natDegree_le _ hA] using hc
theorem cGp (P:n8) (hP:zIT P≤2) :
  0≤(zIU P).coeff 2 :=
 Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
  hP (eventually_eval_affineHilbertPolynomial_nonneg P)
theorem cJU (P:n8) (hP:P ≠ ⊤) (hd:zIT P=2) :
    1≤zHf P:= by
  let H :=zIU P
  change H.natDegree=2 at hd
  have he (x :ℚ) :H.eval x=H.coeff 0+H.coeff 1*x+H.coeff 2*x^2 := by
    rw [Polynomial.eval_eq_sum_range,hd]
    norm_num [zpB]
  obtain ⟨n,hn⟩:=zQf P
  have h (j:ℕ) :H.eval ((n+j:ℕ) :ℚ)=ztr P (n+j) :=
    hn _ (Nat.le_add_right ..)
  have hdiff :2*H.coeff 2 =
      (ztr P (n+2) :ℚ) - 2*(ztr P (n+1) :ℚ) +
        (ztr P (n+0) :ℚ) := by
    rw [← h 0,← h 1,← h 2,he,he,he]
    push_cast
    ring
  have hdeg:zHf P=2*H.coeff 2 := by
    change (H.natDegree.factorial:ℚ)*H.leadingCoeff=2*H.coeff 2
    rw [z4w,hd]
    norm_num
  let z :ℤ:=(ztr P (n+2) :ℤ) -
    2*(ztr P (n+1) :ℤ)+(ztr P (n+0) :ℤ)
  have hz : (z :ℚ)=zHf P:= by
    rw [hdeg,hdiff]
    push_cast [z]
    rfl
  have hp: (0:ℤ)<z := by
    have hpos : (0:ℚ)<(z :ℚ) := by rw [hz]; exact affineDegree_pos hP
    exact_mod_cast hpos
  rw [← hz]
  exact_mod_cast (show (1 :ℤ)≤z by omega)
end
end WI
end
section
namespace bRm
noncomputable section
open dN rW WI MvPolynomial
private theorem aIT {F G:zlg} (hrel :zRK F G) :
  zWc (zVv (zye {F}) G) := by
 apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
 intro x hx
 obtain ⟨D,rfl⟩:=zld x
 rw [← zok,z1Q,Ideal.mem_span_singleton] at hx
 exact Ideal.Quotient.eq_zero_iff_mem.mpr
  (Ideal.mem_span_singleton.mpr (hrel.dvd_of_dvd_mul_left hx))
private theorem aQG {F G:zlg} (hF:F≠0) (hrel :zRK F G)
   {p:n8} (hp: (zye {F} ⊔ zye {G}).IsMinimalPrime p) :
   zIT p=2 := by
 let _:p.IsPrime :=hp.isPrime
 let A:n8:=zye {F}
 obtain ⟨q,hq,hqp⟩:=zXL
   (show A≤p from le_sup_left.trans hp.le)
 let _:q.IsPrime :=hq.isPrime
 have hG:G∉q:= by
   intro h
   obtain ⟨y,hy,hGy⟩:=Ideal.exists_mul_mem_of_mem_minimalPrimes hq h
   apply hy
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   apply aIT hrel
   change zVv A G* zVv A y=zVv A G*0
   rw [← zok,Ideal.Quotient.eq_zero_iff_mem.mpr hGy,znR]
 have hp' : (q ⊔ zye {G}).IsMinimalPrime p:= by
   refine ⟨⟨hp.isPrime,sup_le hqp (le_sup_right.trans hp.le)⟩,fun r hr hrp => ?_⟩
   exact hp.2 ⟨hr.1,sup_le (hq.le.trans (le_sup_left.trans hr.2))
     (le_sup_right.trans hr.2)⟩ hrp
 have hqdeg:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hq
 rw [Nat.card_fin] at hqdeg
 have hpdeg:=principalCut_natDegree_affineHilbertPolynomial_add_one hG hp'
 change zIT q+1=4 at hqdeg
 change zIT p+1=zIT q at hpdeg
 omega
private theorem eJC {F G:zlg} (hF:F≠0) (hrel :zRK F G)
    (hproper : (zye {F} : n8) ≠ ⊤) :
    zIT (zye {F} ⊔ zye {G})≤2 ∧
      2*(zIU (zye {F} ⊔ zye {G})).coeff 2 ≤
        (F.totalDegree :ℚ)*(G.totalDegree :ℚ) := by
  let A:n8:=zye {F}
  have hAdeg:=natDegree_affineHilbertPolynomial_span_singleton_add_one hF hproper
  rw [Nat.card_fin] at hAdeg
  have hthree :zIT A=3:= by
    change zIT A+1=4 at hAdeg
    omega
  have hcoeff :6*(zIU A).leadingCoeff=(F.totalDegree :ℚ) := by
    have hd:zHf A=(F.totalDegree :ℚ) :=affineDegree_span_singleton hF
    unfold zHf at hd
    rw [show (zIU A).natDegree=3 from hthree] at hd
    norm_num at hd
    exact hd
  have hc:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (I:=A) (aIT hrel) (b:=G.totalDegree) zs0
  change (zIU A).natDegree=3 at hthree
  rw [hthree] at hc
  norm_num at hc
  refine ⟨hc.1,?_⟩
  nlinarith only [hc.2,zPw (fun x :ℚ=>x*G.totalDegree) hcoeff]
private theorem exH {J p:n8} (hp:J.IsMinimalPrime p) (hJ:zIT J≤2) :
    ∃ n:ℕ,oA J p hp.isPrime=(n:ℕ∞) ∧
      (n:ℚ)*(zIU p).coeff 2≤(zIU J).coeff 2 := by
  suffices aux : ∀ I:n8,J≤I →
      ∃ n:ℕ,oA I p hp.isPrime=(n:ℕ∞) ∧
        (n:ℚ)*(zIU p).coeff 2≤(zIU I).coeff 2
    from aux J zs0
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α:=n8)) with
  | h I ih =>
    intro hJI
    by_cases hI:I = ⊤
    · subst I
      exact ⟨0,by simpa using aIs hp.isPrime (by simpa using hp.isPrime.ne_top),
        by simp [affineHilbertPolynomial_top]⟩
    obtain ⟨g,hg,hprime⟩:=b2k I hI
    let A:n8:=I.colon {g}
    let B:n8:=I ⊔ zye {g}
    have hIA:I≤A:=Ideal.le_colon
    have hIB:I<B:=lt_of_le_not_ge zPQ
      (fun h=>hg (h (zs1 (z5J g))))
    obtain ⟨n,hn,hbound⟩:=ih B hIB (hJI.trans hIB.le)
    have hdI:=(zy5 hJI).trans hJ
    have hc: (zIU B).coeff 2+(zIU A).coeff 2 ≤
        (zIU I).coeff 2 :=cUM I g hdI
    have hlen:oA I p hp.isPrime=oA A p hp.isPrime+oA B p hp.isPrime :=
      be6 I p hp.isPrime g
    rw [hn] at hlen
    by_cases heq :A=p
    · have hA:oA A p hp.isPrime=1 := by
        rw [heq]
        exact brM p hp.isPrime
      refine ⟨n+1,by simpa [hA,zV6] using hlen,?_⟩
      rw [heq] at hc
      rw [z6H,z4o,add_mul,zkF]
      linarith only [hbound,hc]
    · have hA:oA A p hp.isPrime=0:=aIs hp.isPrime
        (fun hAp=>heq (zWs hAp (hp.2 ⟨hprime,hJI.trans hIA⟩ hAp)))
      refine ⟨n,by simpa [hA] using hlen,?_⟩
      have hnonneg:=cGp A
        ((zy5 hIA).trans hdI)
      linarith only [hbound,hc,hnonneg]
theorem proof :agL.c1 := by
 intro F G p hp hF hrel
 have hspan: (zye {F,G} : n8)=zye {F} ⊔ zye {G} := by
   rw [← Ideal.span_union]
   rfl
 rw [hspan] at hp ⊢
 have hproper : (zye {F} : n8) ≠ ⊤ :=
   ne_top_of_le_ne_top hp.isPrime.ne_top (le_sup_left.trans hp.le)
 obtain ⟨hJ,hupper⟩:=eJC hF hrel hproper
 obtain ⟨n,hn,hlocal⟩:=exH hp hJ
 have hd:=aQG hF hrel hp
 have hdeg:1≤2*(zIU p).coeff 2 := by
   have h:=cJU p hp.isPrime.ne_top hd
   unfold zHf at h
   rw [z4w,show (zIU p).natDegree=2 from hd] at h
   norm_num at h
   exact h
 have hlower : (n:ℚ)≤(n:ℚ)*(2*(zIU p).coeff 2) :=
   le_mul_of_one_le_right (Nat.cast_nonneg _) hdeg
 have hnat :n≤F.totalDegree*G.totalDegree := by
   exact_mod_cast (show (n:ℚ)≤(F.totalDegree :ℚ)*(G.totalDegree :ℚ) by
     linarith only [hlower,hlocal,hupper])
 rw [hn]
 exact_mod_cast hnat
end
end bRm
end
section
namespace ata
noncomputable section
open aR rW NS aRU MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 :Prop :=
  ∀ {k σ:Type} [zrb k] [zTn σ] (B:znc (z3y σ k))
    (ℓ:z3y σ k),
    B.IsHomogeneous (homogeneousSubmodule σ k)→ℓ.IsHomogeneous 1 →
    (∀ P∈zMd (z3y σ k) (z3y σ k ⧸ B),
      (∃ i:σ,z9v i∉P)→ℓ∉P) →
    bze B ℓ
def c2 :Prop :=
  ∀ {k σ:Type} [zrb k] [zTn σ] (I:znc (z3y σ k))
    (a :k) (ℓ:z3y σ k),
    ℓ.IsHomogeneous 1→ zWc (zVv I (C a+ℓ)) →
    bze (lW I) ℓ →
    zIU (cut I (C a+ℓ)) =
      zW9 1 (zIU I)
private theorem cCJ {k σ:Type} [zrb k] [zTn σ]
  (I J:znc (z3y σ k)) (hI:0<zIT I)
  (h:zIU J=zW9 1 (zIU I)) :
  zIT J=zIT I - 1∧zHf J=zHf I:= by
 obtain ⟨hd,hc⟩:=Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
  (zOR : (1 :ℚ)≠0) hI
 refine ⟨by simp only [zIT,h,hd],?_⟩
 have hsucc:zIT I - 1+1=zIT I:= by omega
 have hfact :=zPw Nat.factorial hsucc
 rw [zwO,hsucc] at hfact
 rw [zHf,zHf,h,hd,hc,zkF]
 change _=((zIT I).factorial:ℚ)*_
 rw [← hfact,z2R]
 ring
end
end ata
end
section
namespace bRD
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type} [zrb k]
private theorem d41 [zTn σ]
   (B:znc (z3y σ k)) (ℓ:z3y σ k)
   (hAvoid : ∀ P∈zMd (z3y σ k) (z3y σ k ⧸ B),
     (∃ i:σ,z9v i∉P)→ℓ∉P) :
   ∃ t:ℕ,∀ a∈idealOfVars σ k^t,∀ g,ℓ*g∈B→a*g∈B:= by
 let R:=z3y σ k
 let K:=z83 (LinearMap.lsmul R (R ⧸ B) ℓ)
 have hℓ:ℓ∈zM2 R K:=Module.mem_annihilator.mpr fun x ↦
   zkt (LinearMap.mem_ker.mp x.property)
 have hrad:idealOfVars σ k≤(zM2 R K).radical:= by
   apply Ideal.span_le.mpr
   rintro _ ⟨i,rfl⟩
   rw [SetLike.mem_coe,← Ideal.sInf_minimalPrimes,Ideal.mem_sInf]
   intro P hP
   have hPK:=Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R K hP
   have hPQ:P∈zMd R (R ⧸ B) :=
     associatedPrimes.subset_of_injective K.subtype_injective hPK
   have hle :zM2 R K≤P:= by
     simpa only [Submodule.annihilator_top] using hPK.annihilator_le
   by_contra hi
   exact hAvoid P hPQ ⟨i,hi⟩ (hle hℓ)
 obtain ⟨t,ht⟩:=Ideal.exists_pow_le_of_le_radical_of_fg hrad (idealOfVars_fg σ k)
 refine ⟨t,fun a ha g hg ↦ ?_⟩
 have hgK:zVv B g∈K:= by
   change zVv B (ℓ*g)=0
   exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
 have haK:=Module.mem_annihilator.mp (ht ha) (⟨zVv B g,hgK⟩:K)
 have hzero :zVv B (a*g)=0:=zPw zza haK
 exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
private theorem dOB
    {B:znc (z3y σ k)} (hB:B.IsHomogeneous (homogeneousSubmodule σ k))
    {t n:ℕ} (a g:z3y σ k) (hn:t+g.totalDegree≤n)
    (hann : ∀ b∈idealOfVars σ k^t,b*g∈B) :
    zyc n (a*g)∈B:= by
  classical
  nth_rw 1 [← a.support_sum_monomial_coeff]
  rw [zkr,zdo]
  apply B.sum_mem
  intro d hd
  by_cases h:t≤d.degree
  · exact homogeneousComponent_mem_of_mem hB
      (hann _ ((monomial_mem_pow_idealOfVars_iff t d (mem_support_iff.mp hd)).mpr h)) n
  · have hdeg: (ztt d (a.coeff d)*g).totalDegree<n :=
      (zhM _ _).trans_lt
        ((Nat.add_lt_add_right ((totalDegree_monomial_le d _).trans_lt (Nat.lt_of_not_ge h))
          _).trans_le hn)
    rw [znu n _ hdeg]
    exact B.zero_mem
theorem proof :ata.c1 := by
 classical
 intro k σ _ _ B ℓ hB _ hAvoid
 let R:=z3y σ k
 let J:znc R:=B.colon {ℓ}
 have hJ (g:R) :g∈J↔ℓ*g∈B:= by
  change g∈B.colon {ℓ} ↔ _
  rw [Submodule.mem_colon_singleton,zs5,zDE]
 obtain ⟨t,ht⟩:=d41 B ℓ hAvoid
 obtain ⟨m,g,hg⟩:=Submodule.fg_iff_exists_fin_generating_family.mp
  J.fg_of_isNoetherianRing
 have hgen (i:Fin m) :ℓ*g i∈B :=
  (hJ _).mp (hg ▸ zBO (Set.mem_range_self i))
 let D:=Finset.univ.sup fun i:Fin m ↦ (g i).totalDegree
 refine ⟨t+D,fun n hn q hq hℓq ↦ ?_⟩
 have hqJ:q∈Submodule.span R (Set.range g) :=hg.symm ▸ (hJ _).mpr hℓq
 obtain ⟨a,ha⟩:=(Submodule.mem_span_range_iff_exists_fun R).mp hqJ
 rw [← zoF hq,← ha,zdo]
 apply B.sum_mem
 intro i _
 have hdeg: (g i).totalDegree≤D :=
  zZi (f := fun j ↦ (g j).totalDegree) (zTc i)
 exact dOB hB (a i) (g i)
  ((z3b hdeg t).trans hn) (fun b hb ↦ ht b hb _ (hgen i))
end bRD
end
section
namespace cyN
noncomputable section
open MvPolynomial NS aRU ata
variable {k σ:Type} [zrb k]
private theorem bZ9 {p:z3y σ k} {m:ℕ}
  (hp:p.totalDegree≤ m+1) (hz :zyc (m+1) p=0) :
  p.totalDegree≤ m:= by
 unfold totalDegree
 refine zf9 fun d hd ↦ ?_
 have hle :=(le_totalDegree hd).trans hp
 have hne :d.degree≠m+1 := by
  intro he
  apply mem_support_iff.mp hd
  simpa [coeff_homogeneousComponent,he] using
    zPw (fun q:z3y σ k ↦ q.coeff d) hz
 change d.degree≤ m
 exact Nat.le_of_lt_succ (lt_of_le_of_ne hle hne)
private theorem cA0 (a :k) {ℓ:z3y σ k}
   (hℓ:ℓ.IsHomogeneous 1) : (C a+ℓ).totalDegree≤1 :=
 (totalDegree_add _ _).trans (max_le ((totalDegree_C a).trans_le (by decide)) hℓ.totalDegree_le)
private theorem fVb (I:znc (z3y σ k)) (a :k)
   {ℓ p q:z3y σ k} (hℓ:ℓ.IsHomogeneous 1) {T n:ℕ}
   (hT : ∀ m≥T,∀ r :z3y σ k,r.IsHomogeneous m →
     ℓ*r∈lW I→ r∈lW I)
   (hn:T≤n+1) (hp:p.totalDegree≤n+1)
   (hq:p-(C a+ℓ)*q∈I) :
   ∃ r :z3y σ k,r.totalDegree≤n∧p-(C a+ℓ)*r∈I:= by
 let g:z3y σ k :=C a+ℓ
 have hg:g.totalDegree≤1 :=cA0 a hℓ
 suffices lower : ∀ m (q:z3y σ k),q.totalDegree≤ m→p - g*q∈I →
     ∃ r :z3y σ k,r.totalDegree≤n∧p - g*r∈I from
   lower q.totalDegree q zs0 hq
 intro m
 induction m using Nat.strong_induction_on with
 | h m ih =>
   intro q hqm hq
   by_cases hmn:m≤n
   · exact ⟨q,hqm.trans hmn,hq⟩
   have hhigh:n+1≤ m:= by omega
   have hprod: (g*q).totalDegree≤ m+1 :=
     (zhM _ _).trans (by omega)
   have hdiff : (p - g*q).totalDegree≤ m+1 :=
     (totalDegree_sub _ _).trans (max_le (by omega) hprod)
   have hboundary :zyc (m+1) (p - g*q)∈lW I :=
     zCn ⟨p - g*q,m+1,hq,hdiff,rfl⟩
   have hconst: (C a*q).totalDegree< m+1 :=
     (zhM _ _).trans_lt (by rw [totalDegree_C,zOP]; omega)
   rw [map_sub,homogeneousComponent_eq_zero _ _ (show p.totalDegree< m+1 by omega),
     show g*q=C a*q+ℓ*q from add_mul _ _ _,zrl,
     znu _ _ hconst,zOP,bYu hℓ,
     zero_sub] at hboundary
   have hhom:=z8k m q
   have hlead:=hT m (hn.trans hhigh) (zyc m q) hhom
     ((lW I).neg_mem_iff.mp hboundary)
   obtain ⟨v,hv,hvm,htop⟩ :=
     YT.a5m I hlead m
   have hbound: (q - v).totalDegree≤ m :=
     (totalDegree_sub _ _).trans (max_le hqm hvm)
   have hzero :zyc m (q - v)=0:= by
     rw [zpO,htop,zoF hhom,sub_self]
   have hm:m - 1+1=m:= by omega
   have hsmaller : (q - v).totalDegree≤ m - 1 := by
     apply bZ9
     · rwa [hm]
     · rwa [hm]
   apply ih (m - 1) (by omega) (q - v) hsmaller
   convert I.add_mem hq (I.mul_mem_left g hv) using 1
   ring
private theorem bqT [zTn σ] (I:znc (z3y σ k)) (a :k)
    {ℓ:z3y σ k} (hℓ:ℓ.IsHomogeneous 1)
    (hreg:zWc (zVv I (C a+ℓ))) {T n:ℕ}
    (hT : ∀ m≥T,∀ r :z3y σ k,r.IsHomogeneous m →
      ℓ*r∈lW I→ r∈lW I) (hn:T≤n+1) :
    ztr (cut I (C a+ℓ)) (n+1)+affineHilbertFunction I n =
      ztr I (n+1) := by
  let g:z3y σ k :=C a+ℓ
  let J:=cut I g
  have hIJ:I≤J:=zPQ
  let factor :=z5F k hIJ
  let proj:z9e I (n+1) →ₗ[k] z9e J (n+1) :=
    (factor.toLinearMap.domRestrict _).codRestrict _ fun x ↦ by
      obtain ⟨p,hp,hpx⟩:=mem_quotientDegreeLE.mp x.property
      change factor x.val∈_
      rw [← hpx]
      exact ziU hp
  have hsurj:zpX proj:= by
    intro y
    obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
    exact ⟨⟨zVv I p,ziU hp⟩,zkt hpy⟩
  have hg:g.totalDegree≤1 :=cA0 a hℓ
  let mul :z9e I n →ₗ[k] z9e I (n+1) :=
    ((zzN k (zVv I g)).domRestrict _).codRestrict _ fun x ↦ by
      change zVv I g*x.val∈_
      rw [zg2 n 1]
      exact zan (ziU hg) x.property
  have hmul (x :z9e I n) :mul x∈z83 proj:= by
    rw [zeS]
    apply zkt
    change Ideal.Quotient.factor hIJ (zVv I g*x.val)=0
    have hgJ:g∈J:=zs1 (z5J g)
    rw [zok,Ideal.Quotient.factor_mk,Ideal.Quotient.eq_zero_iff_mem.mpr hgJ,z1S]
  let emb:=mul.codRestrict (z83 proj) hmul
  have hemb:Function.Bijective emb:= by
    constructor
    · intro x y hxy
      exact zkt (hreg
        (zPw (fun z :z83 proj ↦ (z.val :z3y σ k ⧸ I)) hxy))
    · intro y
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.val.property
      have hy :factor y.val.val=0:=zPw zza y.property
      rw [← hpy] at hy
      have hpJ:p∈J:=Ideal.Quotient.eq_zero_iff_mem.mp hy
      obtain ⟨b,hb,t,ht,hsum⟩:=Submodule.mem_sup.mp hpJ
      obtain ⟨q,rfl⟩:=Ideal.mem_span_singleton.mp ht
      have hq:p - g*q∈I:= by rwa [← hsum,add_sub_cancel_right]
      obtain ⟨r,hr,hrI⟩:=fVb I a hℓ hT hn hp hq
      refine ⟨⟨zVv I r,ziU hr⟩,?_⟩
      apply zkt
      apply zkt
      change zVv I g* zVv I r=y.val.val
      rw [← zok,← hpy,Ideal.Quotient.eq]
      simpa only [neg_sub] using I.neg_mem hrI
  have hrank :=proj.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,zl4,
    ← (LinearEquiv.ofBijective emb hemb).finrank_eq] at hrank
  exact hrank
theorem proof :ata.c2 := by
 intro k σ _ _ I a ℓ hℓ hreg hboundary
 obtain ⟨T,hT⟩:=hboundary
 obtain ⟨M,hM⟩:=zQf I
 symm
 apply zpC (N₀:=max T (M+1))
 intro N hN
 have hTn:T≤N :=(zAj T (M+1)).trans hN
 have hMn:M+1≤N :=(zvf T (M+1)).trans hN
 have hsucc:N - 1+1=N := by omega
 have hstep:=bqT I a hℓ hreg hT (n:=N - 1) (by rwa [hsucc])
 rw [hsucc] at hstep
 have hcast: ((N - 1 :ℕ) :ℚ)=(N :ℚ) - 1 := by
  rw [zjK (show 1≤N by omega),z4o]
 rw [Polynomial.eval_backwardDifference,← hcast,hM N (by omega),hM (N - 1) (by omega)]
 apply sub_eq_iff_eq_add.mpr
 exact_mod_cast hstep.symm
end
end cyN
end
section
namespace aY7
noncomputable section
open MvPolynomial MJ agO
variable {k σ τ C E :Type} [zrb k] [za6 C] [zZE k C]
 [za6 E] [zZE k E]
def YG (g:z3y σ k →ₐ[k] C) :z3y σ k →ₐ[k] zM1 C :=
 zIe (fun i=>z1z (g (z9v i))*z7y)
theorem bg0 (g:z3y σ k →ₐ[k] C)
  {p:z3y σ k} {n:ℕ} (hp:p.IsHomogeneous n) :
  YG g p=z1z (g p)*z7y ^n:= by
 classical
 have hm (d:σ →₀ ℕ) (hd:d.degree=n) (a :k) :
    YG g (ztt d a)=z1z (g (ztt d a))*z7y ^n:= by
  have hg:g (ztt d a)=z12 k C a*d.prod (fun i j=>g (z9v i)^j) := by
    rw [zmU (aeval_unique g) (ztt d a),aeval_monomial]
    rfl
  rw [YG,aeval_monomial,hg,Polynomial.algebraMap_apply,zok,ztg]
  simp only [Finsupp.prod,mul_pow,Finset.prod_mul_distrib,← zkq,
    Finset.prod_pow_eq_pow_sum,← zqc,hd,zRa]
 calc
  YG g p = ∑ d∈p.support,YG g (ztt d (p.coeff d)) := by
    rw [← zdo,← p.as_sum]
  _ = ∑ d∈p.support,z1z (g (ztt d (p.coeff d)))*z7y ^n:= by
    apply zUo rfl
    intro d hd
    exact hm d (by simpa only [zqc] using (hp.degree_eq_sum_deg_support hd).symm) (p.coeff d)
  _=z1z (g p)*z7y ^n:= by
    rw [← zkr,← zdo,← zdo,← p.as_sum]
theorem dcc (g:z3y σ k →ₐ[k] C) (p:z3y σ k) (n:ℕ) :
    (YG g p).coeff n=g (zyc n p) := by
  classical
  have h:YG g p =
      ∑ i∈z4x (p.totalDegree+1),
        z1z (g (zyc i p))*z7y ^i:= by
    calc
      YG g p = ∑ i∈z4x (p.totalDegree+1),
          YG g (zyc i p) := by
        rw [← zdo,zjO]
      _ = _:=zUo rfl fun i _ =>
        bg0 g (z8k i p)
  rw [h,zaW]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn:n≤p.totalDegree
  · rw [zi6 n]
    · simp
    · intro i _ hi
      simp [z9m hi]
    · intro hnot
      exact (hnot (Finset.mem_range_succ_iff.mpr hn)).elim
  · rw [znu n p (lt_of_not_ge hn),zhc]
    exact zYF fun i hi=> by
      have hi' := Finset.mem_range_succ_iff.mp hi
      simp [show n≠i by omega]
def ew:z3y (zNO σ) k →ₐ[k] z3y σ k :=
 zIe (fun i=>i.elim 1 z9v)
theorem dVS (p:z3y (zNO σ) k) :
    (ew p).totalDegree≤p.totalDegree := by
  let T:=z0U σ k
  have hT:Monotone T:= fun _ _ h _ hp =>
    (zpJ _ _ _).2 (((zpJ _ _ _).1 hp).trans h)
  have h1 : (1 :z3y σ k)∈T 0:=(zpJ _ _ _).2 (by simp)
  have hm : ∀ i:zNO σ,∀ n t,t∈T n→i.elim 1 z9v*t∈T (n+1) := by
    intro i n t ht
    cases i with
    | none=>simpa using hT (Nat.le_succ n) ht
    | some i =>
      refine (zpJ _ _ _).2 ((zhM _ _).trans ?_)
      simpa [totalDegree_X,zg2] using z3b
        ((zpJ _ _ _).1 ht) 1
  have h:=aeval_mem_of_forall_mul_mem (fun i:zNO σ=>i.elim 1 z9v)
    hT h1 hm (q:=p) zs0
  exact (zpJ _ _ _).1 (by simpa [ew] using h)
def wL (e :zM1 C →ₐ[k] E) (g:z3y σ k →ₐ[k] C) :
    z3y (zNO σ) k →ₐ[k] E :=
  e.comp (YG (g.comp ew))
abbrev Cone (e :zM1 C →ₐ[k] E) (g:z3y σ k →ₐ[k] C) :=
 (wL e g).range
variable (e :zM1 C →ₐ[k] E) (g:z3y σ k →ₐ[k] C)
@[simp] theorem cHD:wL e g (z9v none)=e Polynomial.X:= by
  simp [wL,ew,YG]
@[simp] theorem dOJ (i:σ) :
   wL e g (z9v (some i))=e (z1z (g (z9v i))*z7y) := by
  simp [wL,ew,YG]
def w:Cone e g:=⟨e z7y,⟨z9v none,cHD e g⟩⟩
@[simp] theorem bXu: (w e g:E)=e Polynomial.X:=rfl
def nY:z3y σ k →ₐ[k] Cone e g :=
 (wL e g).rangeRestrict.comp (rename some)
theorem a2B (p:z3y σ k) : (nY e g p:E)=e (YG g p) := by
 have h: (wL e g).comp (rename some)=e.comp (YG g) := by
  apply zpH
  intro i
  simp [YG]
 exact zmU h p
theorem cHA (a :Cone e g) (n:ℕ) :
   ∃ b:zM1 C,e b=(a :E) ∧
     ∃ p:z3y σ k,p.totalDegree≤n∧g p=b.coeff n:= by
 obtain ⟨q,hq⟩:=a.property
 refine ⟨YG (g.comp ew) q,hq,ew (zyc n q),?_,?_⟩
 · exact (dVS (zyc n q)).trans
     (z8k n q).totalDegree_le
 · exact (dcc (g.comp ew) q n).symm
theorem bYz {p:z3y σ k} {n:ℕ} (hp:p.totalDegree≤n) :
   e (z1z (g p)*z7y ^n)∈Cone e g:= by
 classical
 rw [← zjO p,zdo,zdo,zkr,zdo]
 refine (Cone e g).sum_mem fun i hi => ?_
 have hin:i≤n:=(Finset.mem_range_succ_iff.mp hi).trans hp
 rw [← Nat.add_sub_of_le hin,pow_add,← ztg,zok]
 exact (Cone e g).mul_mem
   (by
     rw [← bg0 g (z8k i p),← a2B]
     exact (nY e g _).property)
   (by rw [zkq,← bXu e g]; exact (Cone e g).pow_mem (w e g).property _)
theorem cHG [zTn σ] :IsNoetherianRing (Cone e g) :=
 isNoetherianRing_of_surjective _ _ (wL e g).rangeRestrict.toRingHom
  (wL e g).rangeRestrict_surjective
end
end aY7
end
section
namespace aY7
noncomputable section
open MvPolynomial MJ agO
variable {k σ C E :Type} [zrb k] [za6 C] [zZE k C]
 [za6 E] [zZE k E]
variable (e :zM1 C →ₐ[k] E) (g:z3y σ k →ₐ[k] C)
abbrev i9:=zye ({w e g} : Set (Cone e g))
def a8k :z3y σ k →ₐ[k] Cone e g ⧸ i9 e g :=
 (zvR k _).comp (nY e g)
theorem gny :zpX (a8k e g) := by
  let drop:z3y (zNO σ) k →ₐ[k] z3y σ k :=
    zIe (fun i=>i.elim 0 z9v)
  let q:Cone e g →ₐ[k] Cone e g ⧸ i9 e g:=zvR k _
  have h: (a8k e g).comp drop=q.comp (wL e g).rangeRestrict := by
    apply zpH
    intro i
    cases i with
    | none =>
      have hw: (wL e g).rangeRestrict (z9v none)=w e g :=
        zkt (cHD e g)
      change a8k e g (drop (z9v none))=q ((wL e g).rangeRestrict (z9v none))
      rw [show drop (z9v none)=0 by simp [drop],zhc,hw]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (z5J _)).symm
    | some i=>simp [a8k,drop,nY,q]
  have hsurj:zpX (q.comp (wL e g).rangeRestrict) :=
    (Ideal.Quotient.mk_surjective.comp (wL e g).rangeRestrict_surjective)
  rw [← h] at hsurj
  intro z
  obtain ⟨f,hf⟩:=hsurj z
  exact ⟨drop f,hf⟩
private theorem gB7 (f :z3y σ k) (hf :g f=0) :
    zyc f.totalDegree f∈zdq (a8k e g) := by
  classical
  rw [zry]
  change zVv (i9 e g) (nY e g (zyc f.totalDegree f))=0
  rw [z1Q,Ideal.mem_span_singleton']
  generalize hd:f.totalDegree=d
  cases d with
  | zero =>
    have h:zyc 0 f=f :=
      zoF (isHomogeneous_of_totalDegree_zero σ hd)
    refine ⟨0,?_⟩
    apply zkt
    rw [z1S,Subalgebra.coe_zero,a2B,
      bg0 g (z8k _ _),h,hf]
    simp
  | succ n =>
    let b := ∑ i∈z4x (n+1),zyc i f
    have hsum:b+homogeneousComponent (n+1) f=f := by
      have h:=zjO f
      rw [hd,zpB] at h
      exact h
    have hb:b.totalDegree≤n:= by
      apply (zpJ _ _ _).mp
      exact (z0U σ k n).sum_mem fun i hi =>
        (zpJ _ _ _).mpr
          ((z8k i f).totalDegree_le.trans
            (Finset.mem_range_succ_iff.mp hi))
    have heq :g (zyc (n+1) f)=g (-b) := by
      have hh:=zPw g hsum
      rw [zrl,hf] at hh
      rw [map_neg,eq_neg_iff_add_eq_zero,zV6]
      exact hh
    have hnb: (-b).totalDegree≤n:= by simpa using hb
    refine ⟨⟨_,bYz e g hnb⟩,zkt ?_⟩
    change e (z1z (g (-b))*z7y ^n)*(w e g:E) =
      (nY e g (zyc (n+1) f) :E)
    rw [bXu,← zok,ztg,← zVI,a2B,
      bg0 g (z8k _ _),heq]
theorem gnx (he :zq4 e) :
    zdq (a8k e g)=lW (zdq g.toRingHom) := by
  classical
  refine zWs ?_ (Ideal.span_le.mpr ?_)
  · intro f hf
    have hw:nY e g f∈i9 e g :=
      Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hf)
    obtain ⟨a,ha⟩:=Ideal.mem_span_singleton'.mp hw
    have hc (i:ℕ) (b:zM1 C) (hb:e b=(a :E)) :
        (b*z7y).coeff i=g (zyc i f) := by
      have h:e (b*z7y)=e (YG g f) := by
        rw [zok,hb,← bXu e g,← a2B]
        exact zPw zza ha
      rw [he h,dcc]
    rw [← zjO f]
    refine Ideal.sum_mem _ fun i _ => ?_
    let h:=zyc i f
    have hh:h.IsHomogeneous i:=z8k i f
    change h∈lW (zdq g.toRingHom)
    by_cases hz :h=0
    · simp [hz]
    cases i with
    | zero =>
      obtain ⟨b,hb,_⟩:=cHA e g a 0
      have hhA:h∈zdq g.toRingHom:= by
        rw [zry]
        exact (hc 0 b hb).symm.trans (Polynomial.coeff_mul_X_zero b)
      exact zCn ⟨h,hhA,by rw [hh.totalDegree hz,zoF hh]⟩
    | succ i =>
      obtain ⟨b,hb,p,hp,hpcoef⟩:=cHA e g a i
      have hp' : p.totalDegree< i+1 :=zB1 hp
      have hsub:h - p∈zdq g.toRingHom:= by
        rw [zry,zpO,zF3]
        exact (hc (i+1) b hb).symm.trans ((Polynomial.coeff_mul_X b i).trans hpcoef.symm)
      have hdeg: (h - p).totalDegree=i+1 := by
        rw [sub_eq_add_neg,totalDegree_add_eq_left_of_totalDegree_lt,hh.totalDegree hz]
        simpa [hh.totalDegree hz] using hp'
      exact zCn ⟨h - p,hsub,by
        rw [hdeg,zpO,zoF hh,znu _ _ hp',
          zTY]⟩
  · rintro _ ⟨f,hf,rfl⟩
    exact gB7 e g f (RingHom.mem_ker.mp hf)
variable {g} {A:znc (z3y σ k)}
def aXt (he :zq4 e) (hA:zdq g.toRingHom=A) :
    (z3y σ k ⧸ lW A) ≃ₐ[k] (Cone e g ⧸ i9 e g) :=
  (Ideal.quotientEquivAlgOfEq k ((gnx e g he).trans (zPw lW hA)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (gny e g))
theorem dcn (he :zq4 e) (hA:zdq g.toRingHom=A)
  (f :z3y σ k) :
  aXt e he hA (zVv (lW A) f)=a8k e g f := by
 rfl
def presentation (he :zq4 e) (hA:zdq g.toRingHom=A) :
    a1c (lW A) (w e g) where
  toQuotient:=(aXt e he hA).symm.toRingHom.comp (zVv _)
  surjective :=(aXt e he hA).symm.surjective.comp zld
  ker_eq := by
    rw [RingHom.ker_comp_of_injective _ (aXt e he hA).symm.injective,
     Ideal.mk_ker]
end
end aY7
end
section
namespace aY7
noncomputable section
open MvPolynomial MJ agO
variable {k σ τ C E :Type} [zrb k] [za6 C] [zZE k C]
 [za6 E] [zZE k E]
variable (e :zM1 C →ₐ[k] E) (g:z3y σ k →ₐ[k] C)
 (φ:z3y τ k →ₐ[k] z3y σ k) (hφ:agH φ)
include hφ in
theorem gl0 (p:z3y τ k) :
  YG (g.comp φ) p=YG g (φ p) := by
 suffices YG (g.comp φ)=(YG g).comp φ from zmU this p
 apply zpH
 intro i
 change YG (g.comp φ) (z9v i)=YG g (φ (z9v i))
 rw [bg0 g (hφ i),pow_one]
 simp [YG]
include hφ in
theorem bYA:Cone e (g.comp φ)≤Cone e g:= by
  let lift:z3y (zNO τ) k →ₐ[k] z3y (zNO σ) k :=
    zIe (fun i=>i.elim (z9v none) (fun j=>rename some (φ (z9v j))))
  have h: (wL e g).comp lift=wL e (g.comp φ) := by
    apply zpH
    intro i
    cases i with
    | none=>simp [lift]
    | some i =>
      change wL e g (lift (z9v (some i)))= _
      rw [show lift (z9v (some i))=rename some (φ (z9v i)) by simp [lift]]
      change (nY e g (φ (z9v i)) :E)= _
      simp only [a2B,dOJ,bg0 g (hφ i),
        pow_one,AlgHom.comp_apply]
  rintro _ ⟨p,rfl⟩
  exact ⟨lift p,zmU h p⟩
variable {g} {A:znc (z3y σ k)} {B:znc (z3y τ k)}
include hφ in
theorem eNS (he :zq4 e)
   (hA:zdq g.toRingHom=A) (hB:zdq (g.comp φ).toRingHom=B) :
   Compatible φ.toRingHom (zDu (bYA e g φ hφ)).toRingHom
     (presentation e he hB) (presentation e he hA) := by
 let f :=(zDu (bYA e g φ hφ)).toRingHom
 let qT:=zVv (i9 e (g.comp φ))
 let qS:=zVv (i9 e g)
 let ET:=aXt e he hB
 let ES:=aXt e he hA
 have hf : ∀ x∈i9 e (g.comp φ),qS (f x)=0:= by
   intro x hx
   obtain ⟨a,rfl⟩:=Ideal.mem_span_singleton'.mp hx
   rw [zok,zok]
   have hw:qS (f (w e (g.comp φ)))=0:= by
     change qS (w e g)=0
     exact Ideal.Quotient.eq_zero_iff_mem.mpr (z5J _)
   rw [hw,znR]
 let n:=Ideal.Quotient.lift (i9 e (g.comp φ)) (qS.comp f) hf
 let m:=ES.symm.toRingHom.comp (n.comp ET.toRingHom)
 refine ⟨m,?_,?_⟩
 · apply zz5
   intro p
   change ES.symm (n (ET (zVv (lW B) p))) =
     zVv (lW A) (φ p)
   apply ES.injective
   rw [zIH,dcn e he hB,dcn e he hA]
   change qS (f (nY e (g.comp φ) p))=qS (nY e g (φ p))
   congr 1
   apply zkt
   change (nY e (g.comp φ) p:E)=(nY e g (φ p) :E)
   rw [a2B,a2B,gl0 g φ hφ]
 · apply zz5
   intro p
   change ES.symm (n (ET (ET.symm (qT p))))=ES.symm (qS (f p))
   simp only [zIH,n,qT,Ideal.Quotient.lift_mk,
     zQb]
theorem dOR {F:Type} [ztn C] [zrb F] [zZE k F]
   [zZE (zM1 C) F]
   [z0o (zM1 C) F]
   (eF:zM1 C →ₐ[k] F) (hee : ∀ p,eF p=z12 (zM1 C) F p)
   (hg:zpX g)
   (hbir : ∀ p:z3y σ k,∃ u v :z3y τ k,
     g (φ v)≠0∧g p*g (φ v)=g (φ u)) :
   z0o (Cone eF (g.comp φ)) F:= by
 let T:=Cone eF (g.comp φ)
 let D:=Subfield.closure (T:Set F)
 have he :zq4 eF:= fun a b hab =>
   zxb (zM1 C) F ((hee a).symm.trans (hab.trans (hee b)))
 have hx :eF z7y∈D:=zfX (w eF (g.comp φ)).property
 have hC (a :C) :eF (z1z a)∈D:= by
   obtain ⟨p,rfl⟩:=hg a
   obtain ⟨u,v,hv,huv⟩:=hbir p
   let d:=max u.totalDegree v.totalDegree
   let U:=z1z (g (φ u))*z7y ^d
   let V:=z1z (g (φ v))*z7y ^d
   have hU:eF U∈D:=zfX
     (bYz eF (g.comp φ) (zAj u.totalDegree v.totalDegree))
   have hV:eF V∈D:=zfX
     (bYz eF (g.comp φ) (zvf u.totalDegree v.totalDegree))
   have hV0:eF V≠0:= by
     rw [← zhc eF]
     exact he.ne (zBS (by simpa using hv) (zm1 _ z05))
   have h:eF (z1z (g p))=eF U/eF V:= by
     apply (eq_div_iff hV0).mpr
     rw [← zok]
     apply zPw eF
     dsimp [U,V]
     rw [← ztg,← zok,huv]
   rw [h]
   exact D.div_mem hU hV
 have hpol (p:zM1 C) :eF p∈D:= by
   induction p using zCU with
   | add p q hp hq=>rw [map_add]; exact D.add_mem hp hq
   | monomial n a =>
     rw [← Polynomial.C_mul_X_pow_eq_monomial,zok,zkq]
     exact D.mul_mem (hC a) (D.pow_mem hx n)
 have hmem (z :F) :z∈D:= by
   obtain ⟨p,q,_,rfl⟩:=zJC (zM1 C) z
   rw [← hee,← hee]
   exact D.div_mem (hpol p) (hpol q)
 apply z6t
 intro z
 obtain ⟨x,hx',y,hy',hxy⟩:=Subfield.mem_closure_iff.mp (hmem z)
 have hclosure :Subring.closure (T:Set F)=T.toSubring :=
   Subring.closure_eq T.toSubring
 rw [hclosure] at hx' hy'
 exact ⟨⟨x,hx'⟩,⟨y,hy'⟩,hxy.symm⟩
private theorem eA4 {k σ τ:Type} [zrb k] [zTn σ] [zTn τ]
    (φ:z3y τ k →ₐ[k] z3y σ k) (hφ:agH φ)
    (A:znc (z3y σ k)) (hA:A.IsPrime) (hbir :aRK φ A)
    (F:Type) [zrb F] [zZE (zM1 (z3y σ k ⧸ A)) F]
    [z0o (zM1 (z3y σ k ⧸ A)) F] :
    Nonempty (cxm φ A) := by
  let _:A.IsPrime :=hA
  let C:=z3y σ k ⧸ A
  let P:=zM1 C
  let _:zZE k F:=Algebra.compHom (R:=P) F (z12 k P)
  let _:zsf k P F :=
    zsL (R:=k) (S:=P) (A:=F) (fun _=>rfl)
  let e :=zE2 k P F
  let g:=zvR k A
  have he :zq4 e :=zxb P F
  have hker :zdq g.toRingHom=A:=Ideal.mk_ker
  have hkerφ:zdq (g.comp φ).toRingHom=A.comap φ:= by
    change zdq (g.toRingHom.comp φ.toRingHom)=A.comap φ.toRingHom
    rw [← RingHom.comap_ker,hker]
  refine ⟨{
    F:=F
    target :=Cone e (g.comp φ)
    source :=Cone e g
    le :=bYA e g φ hφ
    targetNoetherian:=cHG e (g.comp φ)
    sourceNoetherian:=cHG e g
    fraction :=dOR (g:=g) φ e (fun _=>rfl) zld ?_
    w:=w e (g.comp φ)
    w_ne := ?_
    targetSection :=presentation e he hkerφ
    sourceSection :=presentation e he hker
    compatible :=eNS e φ hφ he hker hkerφ
  }⟩
  · intro p
    obtain ⟨u,v,hv,huv⟩:=hbir p
    refine ⟨u,v,?_,?_⟩
    · exact fun h=>hv (Ideal.Quotient.eq_zero_iff_mem.mp h)
    · have hh:zVv A (p*φ v-φ u)=0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr huv
      rw [zpO,zok,zF3] at hh
      exact hh
  · intro hw
    have h:e z7y=e 0:= by simpa using zPw zza hw
    exact z05 (he h)
theorem proof :agO.c1 := by
 intro k σ τ _ _ _ φ hφ A hA hbir
 let _:A.IsPrime :=hA
 exact eA4 φ hφ A hA hbir (zNv (zM1 (z3y σ k ⧸ A)))
end
end aY7
end
section
namespace cxP
open Rj
open scoped BigOperators
private def ah5 (w:ℤ) :ℤ:=w^2/4
private def xV (w:ℤ) :ℤ:=ah5 (w+1)
private theorem ZE (w:ℤ) :2*sG w=w*(w+1) := by
 unfold sG
 apply Int.mul_ediv_cancel_of_dvd
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   exact dvd_mul_of_dvd_left (by rw [hw]; exact dvd_mul_right _ _) _
 · have hw:w+1=2*(w/2+1) := by omega
   exact dvd_mul_of_dvd_right (by rw [hw]; exact dvd_mul_right _ _) _
private theorem bKU (w:ℤ) :
   4*ah5 w=w^2 - w % 2 := by
 unfold ah5
 rcases (show w % 2=0∨w % 2=1 by omega) with h | h
 · have hw:w=2*(w/2) := by omega
   have he :w^2=4*(w/2)^2 := by
     calc _=(2*(w/2))^2 :=congrArg (· ^ 2) hw
          _ = _:= by ring
   rw [he,h]
   omega
 · have hw:w=2*(w/2)+1 := by omega
   have he :w^2=4*((w/2)^2+w/2)+1 := by
     calc _=(2*(w/2)+1)^2 :=congrArg (· ^ 2) hw
          _ = _:= by ring
   rw [he,h]
   omega
private theorem awQ (w:ℤ) :
  4*xV w=w^2+2*w+w % 2 := by
 unfold xV
 rw [bKU]
 have h: (w+1) % 2+w % 2=1 := by omega
 nlinarith only [h]
private theorem aJX (w:ℤ) :0≤xV w:= by
 unfold xV ah5
 positivity
private theorem dlN {a b:ℤ} (ha :0≤a) (hab:a≤b) :
  xV a≤xV b:= by
 unfold xV ah5
 have hs : (a+1)^2≤(b+1)^2 := by gcongr
 omega
private theorem bx4 (d:ℤ) :
  sG (d+1)=xV d + xV (d+1) := by
 have hp:d % 2+(d+1) % 2=1 := by omega
 nlinarith only [ZE (d+1),awQ d,awQ (d+1),hp]
private theorem cGS {a w:ℤ} (ha :a≤0) (hw:w≤0) :
  yC ⟨a,w⟩=0:= by
 have hu: (w+1)/2≤0:= by omega
 simp [yC,zWb (max_le ha hu),zWb hw,sG]
private theorem a2L {a w:ℤ} (ha :a≤0) (hw:0≤w) :
   yC ⟨a,w⟩=xV w:= by
 have hu:0≤(w+1)/2 := by omega
 have haw:a≤(w+1)/2 :=ha.trans hu
 have huv : (w+1)/2≤w:= by omega
 have h: (w+1)/2=w/2+w % 2 := by omega
 have h' : w-(w+1)/2=w/2 := by omega
 unfold yC
 simp only [z2J haw,z2J hu,z2J huv]
 rw [h',h]
 have h₁:=ZE (w/2+w % 2)
 have h₂:=ZE (w/2)
 have h₃:=awQ w
 rcases (show w % 2=0∨w % 2=1 by omega) with he | he
 · have hw' : w=2*(w/2) := by omega
   rw [he] at h₁ h₃ ⊢
   conv at h₃=>rhs; rw [hw']
   nlinarith only [h₁,h₂,h₃]
 · have hw' : w=2*(w/2)+1 := by omega
   rw [he] at h₁ h₃ ⊢
   conv at h₃=>rhs; rw [hw']
   nlinarith only [h₁,h₂,h₃]
private theorem cIM {d w:ℤ} (hw:0≤w) (hwd:w≤d) :
  gd d w=xV (w+1) := by
 have hcap:w≤2*d:= by omega
 simp only [gd,not_lt.mpr hw,zMv,zgO hcap,
  zWb (sub_nonpos.mpr hwd)]
 norm_num [xV,ah5,sG,zd8]
private theorem bZf {d w:ℤ} (hd:0≤d) (hdw:d≤w) (hw:w≤2*d) :
  gd d w=sG (d+1) - xV (2*d - w) := by
 simp only [gd,not_lt.mpr (hd.trans hdw),zMv,zgO hw,
  z2J (sub_nonneg.mpr hdw)]
 rw [show (w+2)^2/4=xV (w+1) by
  rw [show w+2=w+1+1 by ring]
  rfl]
 have hp: (w+1) % 2+(2*d - w) % 2=1 := by omega
 nlinarith only [awQ (w+1),awQ (2*d - w),
  ZE (w - d),ZE (d+1),hp]
private theorem bDD {d w:ℤ} (hd:0≤d) (hw:2*d≤w) :
   gd d w=sG (d+1) := by
 have h:gd d w=gd d (2*d) := by
   simp [gd,not_lt.mpr (show 0≤2*d by omega),
     not_lt.mpr (show 0≤w by omega),zmZ hw]
 rw [h,bZf hd (by omega) zs0]
 simp [xV,ah5]
private theorem cII {d:ℤ} (hd:0≤d) (w:ℤ) :
   0≤gd d w∧gd d w≤ sG (d+1) := by
 by_cases hw:w<0
 · simp [gd,hw,bx4,add_nonneg (aJX _) (aJX _)]
 by_cases hwd:w≤d
 · rw [cIM (by omega) hwd,bx4]
   have h:=dlN (a :=w+1) (b:=d+1) (by omega) (by omega)
   exact ⟨aJX _,by linarith [aJX d]⟩
 by_cases hcap:w≤2*d
 · rw [bZf hd (by omega) hcap,bx4]
   have h:=dlN (a :=2*d - w) (b:=d) (by omega) (by omega)
   exact ⟨by linarith [aJX (d+1)],by linarith [aJX (2*d - w)]⟩
 · rw [bDD hd (by omega),bx4]
   exact ⟨add_nonneg (aJX _) (aJX _),zs0⟩
private def aHO (n:ℕ) :kJ:= fun i=>if i=4 then n else 0
private def b4a (q k :ℕ) :kJ :=
 aHO (Ic q (zve k)-(q:ℤ)).toNat
private theorem agp (n:ℕ) (f :Fin 6→ℤ) :
  (∑ i,(aHO n i:ℤ)*f i)=(n:ℤ)*f 4 := by
 simp [aHO]
private theorem dd0 (q n:ℕ) (g:ℤ) (hq:q<1151) (hg:0≤g)
   (hn:n≤q) (ht:0≤Ic q g - 2*(n:ℤ)) :
   m5 (K6 q (aHO n)) (D8 q g (aHO n)) =
     sG ((q:ℤ) - n+1) - xV (Ic q g - 2*(n:ℤ)) := by
 have hd:iO q=q:=zgO (by omega)
 have hd' : K6 q (aHO n)=(q:ℤ) - n:= by
   rw [K6,hd,agp]
   simp [yE]
 have hP:D8 q g (aHO n) 0=⟨0,-g⟩:= by
   simp [D8,agp,pT,Jd]
 have hQ:D8 q g (aHO n) 1=⟨(q:ℤ) - 1150,2*(q:ℤ) - 2300⟩:= by
   simp [D8,agp,pT,Jd,hd]
 have hO:D8 q g (aHO n) 2=⟨-(n:ℤ),Ic q g - 2*(n:ℤ)⟩:= by
   simp [D8,agp,pT,Jd,zDE]
 rw [m5,hd']
 simp only [show ¬ ((q:ℤ) - n)<0 by omega,ite_false,Fin.sum_univ_three,hP,hQ,hO,
   cGS (a :=0) (w := -g) (by omega) (by omega),
   cGS (a :=(q:ℤ) - 1150) (w:=2*(q:ℤ) - 2300) (by omega) (by omega),
   a2L (a := -(n:ℤ)) (by omega) ht,zOP]
private theorem bmM {a b:ℤ} (hab:a≤b) (hb:0≤b) :
  (a.toNat :ℤ)≤b:= by
 have h:=z0Z hab
 omega
private theorem dzm (q:ℕ) (g:ℤ) (p:kJ) (h:0≤Bb q g) :
   (xR q g p:ℤ)≤Bb q g:= by
 by_cases ht:Ic q g≤0
 · simpa only [xR,ht,ite_true,zQq] using h
 simp only [xR,ht,zMv]
 apply bmM _ h
 exact sub_le_self _ (zAj _ _)
private theorem dzr (q:ℕ) (g:ℤ) (p:kJ) (r :ℤ) (hr :0≤ r)
    (h:Bb q g -
        m5 (K6 q p) (D8 q g p)≤ r) :
    (xR q g p:ℤ)≤ r := by
  by_cases ht:Ic q g≤0
  · simpa only [xR,ht,ite_true,zQq] using hr
  simp only [xR,ht,zMv]
  apply bmM _ hr
  exact (sub_le_sub_left ((zvf _ _).trans (zvf _ _)) _).trans h
private theorem dzn (q k :ℕ) (hq:q<1151) :
   (xR q (zve k) (b4a q k) :ℤ) ≤
     gd q (Ic q (zve k) - 1) - gd q (-offset k - 1) := by
 let g:=zve k
 let t:=Ic q g
 change (xR q g (aHO (t - (q:ℤ)).toNat) :ℤ) ≤
   gd q (t - 1) - gd q (-g - 1)
 have hq0: (0:ℤ)≤q:= by positivity
 have hc:Bb q g=sG ((q:ℤ)+1) - gd q (-g - 1) := by
   have hd:iO q=q:=zgO (by omega)
   have hg : -g - 1≤2300:= by dsimp [g,zve]; omega
   unfold Bb
   rw [hd,zmZ hg]
   change gd (q:ℤ) 2300 - gd q (-g - 1)= _
   rw [bDD hq0 (by omega :2*(q:ℤ)≤2300)]
 by_cases hhigh:2*(q:ℤ)<t
 · rw [bDD hq0 (by omega),← hc]
   exact dzm _ _ _ (by rw [hc]; exact sub_nonneg.mpr (cII hq0 _).2)
 have hg:0≤g:= by unfold t Ic at hhigh; omega
 have hz :gd q (-g - 1)=0:= by simp [gd,show -g - 1<0 by omega]
 rw [hz,zTY]
 by_cases ht:t≤0
 · simp [xR,show Ic q g≤0 from ht,gd,show t - 1<0 by omega]
 apply dzr _ _ _ _ (cII hq0 _).1
 rw [hc,hz,zTY]
 by_cases hlo:t≤(q:ℤ)
 · have hn: (t - (q:ℤ)).toNat=0:= by omega
   rw [hn,dd0 q 0 g hq hg (by omega) (by simpa [t] using le_of_lt (lt_of_not_ge ht)),
     cIM (by omega) (by omega)]
   push_cast
   simp only [zTY]
   rw [show t - 1+1=t by ring]
   change sG ((q:ℤ)+1)-(sG ((q:ℤ)+1) - xV t)≤xV t
   linarith
 have hn: ((t - (q:ℤ)).toNat :ℤ)=t - (q:ℤ) :=zi4 (by omega)
 rw [dd0 q _ g hq hg (by omega) (by change 0≤t - _; omega),
   hn,bZf hq0 (by omega) (by omega)]
 change sG ((q:ℤ)+1) -
   (sG ((q:ℤ)-(t - (q:ℤ))+1) - xV (t - 2*(t - (q:ℤ))))≤_
 rw [show (q:ℤ)-(t - (q:ℤ))+1=2*(q:ℤ) - t+1 by ring,
   show t - 2*(t - (q:ℤ))=2*(q:ℤ) - t by ring,
   bx4 (2*(q:ℤ) - t),
   show 2*(q:ℤ)-(t - 1)=2*(q:ℤ) - t+1 by ring]
 linarith
private theorem sum_reverse (d:ℤ) (n N :ℕ) (hn:n≤N) :
    (∑ k∈z4x N,gd d ((n:ℤ) - 1-(k :ℤ))) =
      ∑ k∈z4x n,gd d (k :ℤ) := by
  calc
    _ = ∑ k∈z4x n,gd d ((n:ℤ) - 1-(k :ℤ)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hn)
      intro k _ hk
      have hneg: (n:ℤ) - 1-(k :ℤ)<0:= by
        simp only [Finset.mem_range] at hk
        omega
      simp [gd,hneg]
    _ = _:= by
      rw [← Finset.sum_range_reflect (fun k :ℕ=>gd d (k :ℤ)) n]
      apply zUo rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      congr 1
      omega
private def bej (q:ℕ) :ℤ:=(5000-(q:ℤ))*sG ((q:ℤ)+1)
private theorem eiL (q:ℕ) (hq:q<1151) :
    (Xi b4a q:ℤ)≤bej q:= by
  rw [ Xi,zCt]
  calc
    _ ≤ ∑ k∈z4x 7300,
        (gd (q:ℤ) (Ic q (zve k) - 1) - gd (q:ℤ) (-offset k - 1)) :=
      zQk fun k _=>dzn q k hq
    _=bej q:= by
      have hp (k :ℕ) :Ic q (zve k) - 1=((7300 - q:ℕ) :ℤ) - 1 - k := by
        unfold Ic zve
        omega
      have hm (k :ℕ) : -offset k - 1=((2300:ℕ) :ℤ) - 1 - k := by
        unfold zve
        omega
      simp_rw [hp,hm]
      rw [zQr,sum_reverse _ _ _ (Nat.sub_le _ _),
        sum_reverse _ _ _ (by omega :2300≤7300),
        show 7300 - q=2300+(5000 - q) by omega,Finset.sum_range_add,add_sub_cancel_left]
      have hfull (k :ℕ) :gd (q:ℤ) ((2300+k :ℕ) :ℤ) =
          sG ((q:ℤ)+1) :=bDD (by omega) (by omega)
      simp_rw [hfull]
      simp [bej,zjK (show q≤5000 by omega)]
private theorem gwN (n:ℕ) :
   24*(∑ q∈z4x n,bej q) =
    (n:ℤ)*(n+1)*(n+2)*(20003-3*(n:ℤ)) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [zpB,mul_add,ih,bej,zg0]
   have ht:=ZE ((n:ℤ)+1)
   linear_combination 12*(5000-(n:ℤ))*ht
theorem proof :Rj.c3:= by
 refine ⟨b4a,?_⟩
 have h: (∑ q∈z4x 1151,bej q)=1054250623200:= by
  have hs :=gwN 1151
  norm_num only [Nat.cast_ofNat,Int.reduceAdd,Int.reduceMul,Int.reduceSub] at hs
  omega
 have hsum:=zQk (s :=z4x 1151)
  (fun q hq=>eiL q (Finset.mem_range.mp hq))
 rw [← zCt,h] at hsum
 exact_mod_cast hsum
end cxP
end
section
set_option linter.style.haveILetI false
namespace YT
noncomputable section
open aR we aiJ NS MvPolynomial
private def ZM (Q:Bk) :
  (nW ⧸ lA Q) →ₐ[dF] (mK ⧸ gN Q) :=
 Ideal.quotientMapₐ (gN Q) tO (fun _ h=>h)
private theorem aDt (Q:Bk) (p:nW) :
 ZM Q (zVv (lA Q) p) =
  zVv (gN Q) (tO p) :=rfl
private theorem brl (Q:Bk) (j:Fin 3) :
   ZM Q (zVv (lA Q) (z9v j)) =
     zVv (gN Q) (B7.KT adE j.val) := by
 rw [aDt,tO,zTw]
private theorem b6L (Q:Bk) :zq4 (ZM Q) := by
 apply (injective_iff_map_eq_zero (ZM Q)).mpr
 intro z hz
 obtain ⟨p,rfl⟩:=zld z
 rw [aDt,z1Q] at hz
 exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
private theorem fU2 {Q:Bk} (hP: (gN Q).IsPrime)
   (hb:asY Q) (x :mK ⧸ gN Q) :
   ∃ a b,ZM Q b≠0∧ZM Q b*x=ZM Q a := by
 letI:=hP
 let g:=ZM Q
 have hX (i:Fin bf) :
     ∃ a b,g b≠0∧g b* zVv (gN Q) (z9v i)=g a := by
   obtain ⟨u,v,hv,huv⟩:=hb i
   refine ⟨zVv _ u,zVv _ v,?_,?_⟩
   · rwa [show g=ZM Q from rfl,aDt,Ne,z1Q]
   · rw [show g=ZM Q from rfl,aDt,aDt,← zok,← zF3,← zpO]
     exact Ideal.Quotient.eq_zero_iff_mem.mpr huv
 obtain ⟨p,rfl⟩:=zld x
 change ∃ a b,g b≠0∧g b* zVv (gN Q) p=g a
 induction p using MvPolynomial.induction_on with
 | C c =>
   refine ⟨z12 dF _ c,1,by simp,?_⟩
   rw [zXs,zkF,AlgHom.commutes]
   rfl
 | add p q hp hq =>
   obtain ⟨a,b,hb₀,ha⟩:=hp
   obtain ⟨c,d,hd₀,hc⟩:=hq
   refine ⟨a*d+b*c,b*d,by simpa only [zok] using zBS hb₀ hd₀,?_⟩
   simp only [zok,zrl]
   rw [show g b*g d*(zVv (gN Q) p +
     zVv (gN Q) q) =
     (g b* zVv (gN Q) p)*g d +
     g b*(g d* zVv (gN Q) q) by ring,ha,hc]
 | mul_X p i hp =>
   obtain ⟨a,b,hb₀,ha⟩:=hp
   obtain ⟨c,d,hd₀,hc⟩:=hX i
   refine ⟨a*c,b*d,by simpa only [zok] using zBS hb₀ hd₀,?_⟩
   simp only [zok]
   rw [show g b*g d*(zVv (gN Q) p *
     zVv (gN Q) (z9v i)) =
     (g b* zVv (gN Q) p) *
     (g d* zVv (gN Q) (z9v i)) by ring,ha,hc]
theorem proof :aiJ.c2 := by
  intro Q _ hd hp hb
  letI:=hp
  let g:=ZM Q
  have hrec:=fU2 hp hb
  have hg:=b6L Q
  have hbase :zIU (gN Q)=zIU Q :=
    Ey.ZI Q
  have hdim_ext: (zIU (gN Q)).natDegree=1 := by
    rwa [hbase]
  have hlin (j:Fin 3) :
      g (zVv (lA Q) (z9v j)) ∈
        z9e (gN Q) 1 := by
    change ZM Q _∈_
    rw [brl]
    exact ziU (b6H j.val).totalDegree_le
  have hdim_le :=(natDegree_affineHilbertPolynomial_le_of_injective g hg).trans_eq hdim_ext
  have hdim: (zIU (lA Q)).natDegree=1 := by
    by_contra hd'
    have hz : (zIU (lA Q)).natDegree=0:= by omega
    letI: (lA Q).IsPrime :=hp.comap tO
    letI:=moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hz
    have hsurj:zpX g:= by
      intro x
      obtain ⟨a,b,hb₀,he⟩:=hrec x
      obtain ⟨c,hc⟩:=FiniteDimensional.exists_mul_eq_one dF
        (show b≠0 from fun h=>hb₀ (by simp [h]))
      refine ⟨c*a,?_⟩
      rw [zok,← he,← ztg,← zok,zDE c b,hc,zXs,zkF]
    have h:=natDegree_affineHilbertPolynomial_le_of_surjective g hsurj
    rw [hdim_ext,hz] at h
    omega
  have hdeg:=cJY g hg (0:Fin 3) (brl Q 0) hlin
    hrec (ed6 Q hd)
  refine ⟨hdim,?_⟩
  rw [← hdeg,zHf,zHf,hbase]
end
end YT
end
section
namespace aKs
noncomputable section
open aR dN Kd MvPolynomial
private def a4w {ι:Type} [z85 ι] :
  (ι→ℕ) ≃+ (ι →₀ ℕ) :=
 Finsupp.addEquivFunOnFinite.symm
private theorem ehU {ι:Type} [z85 ι] [zRw ι] (i:ι) :
  a4w (step i)=zhf i 1 :=
 Finsupp.equivFunOnFinite_symm_single i 1
private theorem dEG {ι:Type} (fF:ι→Shape) (J:znc zlg)
  (v :Kb fF) :
  zxY fF J (z9v v)=ztt (zhf v.1 1)
    (zVv J (ztt v.2.val 1)) :=
 zTw _ _
private theorem bCa {ι:Type} [z85 ι] [zRw ι]
    (fF:ι→Shape) (J:znc zlg) (e :Kb fF →₀ ℕ) :
    zxY fF J (ztt e 1) =
      ztt (a4w (ztN (step ∘ Fd fF) e))
        (zVv J (ztt (ztN (fun v :Kb fF=>v.2.val) e) 1)) := by
  induction e using Finsupp.induction_linear with
  | zero=>simp [monomial_zero']
  | add e f he hf =>
      rw [← zkF (1 :zA7),← zDU,zok,he,hf,
        zDU,← zok,zDU,zkF,
        zrl,zrl,zrl]
  | single v n =>
      rw [← X_pow_eq_monomial,zkq,dEG,zpV,← zkq,
        zpV,one_pow,zTy,zTy,map_nsmul]
      change ztt (n•zhf v.1 1)
        (zVv J (ztt (n•v.2.val) 1)) =
        ztt (n•a4w (step v.1))
          (zVv J (ztt (n•v.2.val) 1))
      rw [ehU]
private theorem dEF {ι:Type} [z85 ι] [zRw ι]
    (fF:ι→Shape) (J:znc zlg) :
    aiD (Fd fF) (HW fF J) := by
  intro f hf a
  classical
  let proj:z3y ι (zlg ⧸ J) →ₗ[zA7] z3y ι (zlg ⧸ J) :=
    ((ztt (a4w a)).comp (lcoeff (zlg ⧸ J) (a4w a))).restrictScalars
      zA7
  have hcomm :
      (zxY fF J).toLinearMap.comp
          (weightedHomogeneousComponent (step ∘ Fd fF) a) =
        proj.comp (zxY fF J).toLinearMap:= by
    apply (basisMonomials (Kb fF) zA7).ext
    intro e
    simp only [coe_basisMonomials,zoD,zJr]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial
      (step ∘ Fd fF) e 1 rfl)]
    by_cases he :ztN (step ∘ Fd fF) e=a
    · simp [he,proj,bCa]
    · simp [he,z9m he,proj,bCa]
  change zxY fF J f=0 at hf
  change zxY fF J (weightedHomogeneousComponent (step ∘ Fd fF) a f)=0
  have hf' := zmU hcomm f
  simpa only [zoD,zJr,hf,zhc] using hf'
private theorem dE3 {ι:Type} [z85 ι] [zRw ι]
    (fF:ι→Shape) (J:znc zlg) (a :ι→ℕ) :
    lO (Fd fF) (HW fF J) a =
      (Sn J (Yz fF a) :ℚ) := by
  let S:=weightedHomogeneousSubmodule zA7 (step ∘ Fd fF) a
  let V:=S.map (zvR zA7 (zdq (zxY fF J))).toLinearMap
  let T:=zQW zA7 (Yz fF a)
  let U:=T.map (zvR zA7 J).toLinearMap
  let lift:=(Ideal.kerLiftAlg (zxY fF J)).toLinearMap
  let tag : (zlg ⧸ J) →ₗ[zA7] z3y ι (zlg ⧸ J) :=
    (ztt (a4w a)).restrictScalars zA7
  have hlift:V.map lift=S.map (zxY fF J).toLinearMap:= by
    change (S.map _).map _ = _
    rw [← Submodule.map_comp]
    rfl
  have htag :zq4 tag := by
    intro x y h
    have hc:=zPw (fun p:z3y ι (zlg ⧸ J)=>p.coeff (a4w a)) h
    simpa [tag] using hc
  have himage :S.map (zxY fF J).toLinearMap=U.map tag := by
    have hS:S=zQW zA7
        {e | ztN (step ∘ Fd fF) e=a} :=
      weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
    change S.map _=(T.map _).map _
    rw [hS,show T=zQW zA7 (Yz fF a) from rfl,
      restrictSupport_eq_span,restrictSupport_eq_span,zYZ,
      zYZ,zYZ]
    congr 1
    ext p
    constructor
    · rintro ⟨_,⟨e,he,rfl⟩,rfl⟩
      change ztN (step ∘ Fd fF) e=a at he
      refine ⟨_,⟨_,⟨_,⟨e,he,rfl⟩,rfl⟩,rfl⟩,?_⟩
      simp only [zJr,bCa,he]
      rfl
    · rintro ⟨_,⟨_,⟨m,hm,rfl⟩,rfl⟩,rfl⟩
      obtain ⟨e,he,rfl⟩:=hm
      refine ⟨_,⟨e,he,rfl⟩,?_⟩
      simp only [zJr,bCa,he]
      rfl
  have hrank :zsE zA7 V=zsE zA7 U :=
    calc
      _=zsE zA7 (V.map lift) :=
        (zW6 lift (Ideal.kerLiftAlg_injective (zxY fF J))
          V).finrank_eq
      _=zsE zA7 (U.map tag) := by rw [hlift,himage]
      _ = _:=(zW6 tag htag U).finrank_eq.symm
  exact zPw (fun n:ℕ=>(n:ℚ)) hrank
theorem proof :Kd.c3:= by
 intro ι _ _ fF J
 exact ⟨dEF fF J,dE3 fF J⟩
end
end aKs
end
section
namespace aY5
open Polynomial E7
open scoped Polynomial WithZero
noncomputable section
variable {F L:Type} [zrb F] [zrb L]
def DZ (e :F[X] →+* L) (i:ℕ) (g:F[X]) :L :=
 e (z75 i g)/e g
theorem epX (e :F[X] →+* L) {g:F[X]} (hg:e g≠0) :
  DZ e 0 g=1 := by
 simp [DZ,hg]
theorem cVX (e :F[X] →+* L) {g h:F[X]} (hg:e g≠0) (hh:e h≠0) :
   DZ e 1 (g*h)=DZ e 1 g+DZ e 1 h ∧
   DZ e 2 (g*h) =
    DZ e 2 g+DZ e 1 g*DZ e 1 h+DZ e 2 h:= by
 have h₁:z5G 1 = {(0,1),(1,0)} := by decide
 have h₂:z5G 2 = {(0,2),(1,1),(2,0)} := by decide
 constructor
 · unfold DZ
   rw [hasseDeriv_mul,h₁]
   simp
   field_simp
   ring
 · unfold DZ
   rw [hasseDeriv_mul,h₂]
   simp
   field_simp
   ring
theorem epW (e :F[X] →+* L) {g:F[X]} (hg:e g≠0) (m:ℕ) :
   DZ e 1 (g^m)=(m:L)*DZ e 1 g ∧
   DZ e 2 (g^m) =
     (m:L)*DZ e 2 g+(m.choose 2 :L)*DZ e 1 g^2 := by
 induction m with
 | zero =>
   simp [DZ,hasseDeriv_apply_one]
 | succ m ih =>
   have hm:e (g^m)≠0:= by simpa using zm1 m hg
   obtain ⟨h₁,h₂⟩:=cVX e hm hg
   have hc: ((m+1).choose 2 :L)=(m:L)+(m.choose 2 :L) := by
     rw [Nat.choose_succ_succ',zk3,z6H]
   constructor
   · rw [zVI,h₁,ih.1,zg0]
     ring
   · rw [zVI,h₂,ih.1,ih.2,hc,zg0]
     ring
theorem cMZ (j:F →+* L) (a :L) (v :zfZ L ℤᵐ⁰) (ha :v a=1)
    (g:F[X]) (i:ℕ) {w:ℤᵐ⁰} (hw : ∀ n∈g.support,v (j (g.coeff n))≤w) :
    v ((z75 i g).eval₂ j a)≤w:= by
  rw [hasseDeriv_apply,Polynomial.sum,eval₂_finsetSum]
  apply v.map_sum_le
  intro n hn
  simp only [eval₂_monomial,zok,zkq,ha,one_pow,zqe]
  have hcast:v (j (n.choose i:F))≤1 := by
    have hn : ∀ m:ℕ,v (m:L)≤1 := by
      intro m
      induction m with
      | zero=>simp
      | succ m hm =>
        rw [zg0]
        exact v.map_add_le hm (by simp)
    simpa only [zGu] using hn (n.choose i)
  simpa only [zkF] using mul_le_mul_of_nonneg hcast (hw n hn) zJK zJK
theorem cMR (e :F[X] →+* L) (v :zfZ L ℤᵐ⁰)
  {g h:F[X]} (hint : ∀ p,v (e p)≤1) (hcop:IsCoprime g h)
  (hg:v (e g)<1) :v (e h)=1 := by
 obtain ⟨p,q,hpq⟩:=hcop
 refine (hint h).antisymm (zHm fun hh => ?_)
 have hmul {p g:F[X]} (hg:v (e g)<1) :v (e p*e g)<1 := by
  rw [zok]
  exact (zZD zJK (hint p)).trans_lt hg
 have h₀:v (e p*e g+e q*e h)<1 :=
  v.map_add_lt (hmul hg) (hmul hh)
 rw [← zok,← zok,← zrl,hpq,zXs,zXs] at h₀
 exact (lt_irrefl _ h₀)
end
end aY5
end
section
namespace aY5
open Polynomial E7
open scoped Polynomial WithZero
noncomputable section
variable {F L:Type} [zrb F] [zrb L]
private theorem c4w (v :zfZ L ℤᵐ⁰) {x :L}
   {w:ℤᵐ⁰} (hw:w≠0) (h:v x≤w) :zbb v x≤(zx3 w).toNat := by
 unfold zbb
 by_cases hx :v x=0
 · simp [hx]
 exact z0Z ((WithZero.log_le_log hx hw).2 h)
theorem cb8 (v :zfZ L ℤᵐ⁰) {x :L} (h:v x≤1) :
  zbb v x=0 :=
 za7 (by simpa using c4w v zOR h)
private theorem dii {σ:Type} [z85 σ] (v :zfZ L ℤᵐ⁰)
  (u:σ→L) {w:ℤᵐ⁰} (hw:w≠0) (h : ∀ i,v (u i)≤w) :
  Tq v u≤(zx3 w).toNat :=
 zf9 (fun i _=>c4w v hw (h i))
theorem dih {σ:Type} [z85 σ] (v :zfZ L ℤᵐ⁰)
  (u:σ→L) {w:ℤᵐ⁰} (hw:w≠0) (h : ∀ i,v (u i)≤w)
  (he : ∃ i,v (u i)=w) :Tq v u=(zx3 w).toNat := by
 refine (dii v u hw h).antisymm ?_
 obtain ⟨i,hi⟩:=he
 rw [← hi]
 exact zZi (s :=zdB) (f := fun j=>zbb v (u j)) (zTc i)
theorem cum {σ:Type} [z85 σ] (v :zfZ L ℤᵐ⁰)
  (u:σ→L) (h : ∀ i,v (u i)≤1) :Tq v u=0 :=
 za7 (by simpa using dii v u zOR h)
theorem cw4 (v :zfZ L ℤᵐ⁰) {x :L} (h:1≤v x) :
  KB v x=0:= by
 have hlog:0≤zx3 (v x) :=zeE (by simpa using h)
 unfold KB
 omega
theorem ex6 {ι:Type} (s :zJe ι) (w:ι→ℤᵐ⁰)
   (h : ∀ i∈s,1≤w i) :
   (zx3 (∏ i∈s,w i)).toNat = ∑ i∈s,(zx3 (w i)).toNat := by
 classical
 induction s using Finset.induction_on with
 | empty=>simp
 | @insert i s hi ih =>
   have hw:1≤w i:=h i (Finset.mem_insert_self i s)
   have hs k (hk :k∈s) :1≤w k :=h k (Finset.mem_insert_of_mem hk)
   have hp:1 ≤ ∏ k∈s,w k :=z9l hs
   have h₁:0≤zx3 (w i) :=zeE (by simpa using hw)
   have h₂:0≤zx3 (∏ k∈s,w k) :=
     zeE (by simpa using hp)
   rw [Finset.prod_insert hi,Finset.sum_insert hi,← ih hs,
     WithZero.log_mul (zero_lt_one.trans_le hw).ne' (zero_lt_one.trans_le hp).ne']
   omega
theorem cYN (w:ℤᵐ⁰) (m:ℕ) (h:1≤w) :
   (zx3 (w^m)).toNat=m*(zx3 w).toNat := by
 have hlog:0≤zx3 w:=zeE (by simpa using h)
 rw [WithZero.log_pow,nsmul_eq_mul]
 have hm:0≤(m:ℤ)*zx3 w:=mul_nonneg (Int.natCast_nonneg _) hlog
 exact_mod_cast (show (((m:ℤ)*zx3 w).toNat :ℤ) =
     ↑(m*(zx3 w).toNat) by simp [zi4 hm,zi4 hlog])
theorem exI (e :F[X] →+* L) (v :zfZ L ℤᵐ⁰) (g h:F[X]) (m:ℕ)
    (hm:0< m) (hg:e g≠0) (hz :v (e g)<1)
    (hd:v (e (z75 1 g))=1) (hh:v (e h)=1)
    (hint : ∀ p i,v (e (z75 i p))≤1)
    (hc₁:v (m:L)=1) (hc₂:2≤ m→v (m.choose 2 :L)=1) :
    (∀ i:Fin 3,v (DZ e i.val (g^m*h))≤(v (e g))⁻¹^min m 2) ∧
      ∃ i:Fin 3,v (DZ e i.val (g^m*h))=(v (e g))⁻¹^min m 2 := by
  let T:=(v (e g))⁻¹
  have hT:1<T:=(one_lt_inv₀ ((v.ne_zero_iff.2 hg).bot_lt)).2 hz
  have hhn:e h≠0:=v.ne_zero_iff.1 (hh.trans_ne zOR)
  have hgn:e (g^m)≠0:= by simpa using zm1 m hg
  have hfn :e (g^m*h)≠0:= by simpa only [zok] using zBS hgn hhn
  have hr₀:v (DZ e 0 (g^m*h))=1 := by rw [epX e hfn,zXs]
  have hG₁:v (DZ e 1 g)=T:= by rw [DZ,v.map_div,hd,one_div]
  have hG₂:v (DZ e 2 g)≤T:= by
    rw [DZ,v.map_div,div_eq_mul_inv]
    exact zZD zJK (hint g 2)
  have hH (i:ℕ) :v (DZ e i h)≤1 := by
    rw [DZ,v.map_div,hh,div_one]
    exact hint h i
  have hmul {x y :L} (hx :v x≤1) (hy :v y≤T) :v (x*y)≤T:= by
    rw [zok]
    exact (zZD zJK hx).trans hy
  obtain ⟨hp₁,hp₂⟩:=epW e hg m
  obtain ⟨hf₁,hf₂⟩:=cVX e hgn hhn
  rw [hp₁] at hf₁
  have hleft:v ((m:L)*DZ e 1 g)=T:= by rw [zok,hc₁,hG₁,zkF]
  have hR₁:v (DZ e 1 (g^m*h))=T:= by
    rw [hf₁,v.map_add_eq_of_lt_left ((hH 1).trans_lt (hT.trans_eq hleft.symm)),hleft]
  have hR₂:DZ e 2 (g^m*h)=(m.choose 2 :L)*DZ e 1 g^2 +
      ((m:L)*DZ e 2 g+DZ e 2 h +
        DZ e 1 h*((m:L)*DZ e 1 g)) := by
    rw [hf₂,hp₁,hp₂]
    ring
  have hsmall:v ((m:L)*DZ e 2 g+DZ e 2 h +
        DZ e 1 h*((m:L)*DZ e 1 g))≤T :=
    v.map_add_le (v.map_add_le (hmul hc₁.le hG₂) ((hH 2).trans hT.le))
      (hmul (hH 1) hleft.le)
  by_cases h₂:2≤ m
  · have hTT:T<T^2 := by
      rw [pow_two]
      exact lt_mul_of_one_lt_right (zero_lt_one.trans hT) hT
    have hmain:v ((m.choose 2 :L)*DZ e 1 g^2)=T^2 := by
      rw [zok,zkq,hc₂ h₂,hG₁,zkF]
    have hR₂' : v (DZ e 2 (g^m*h))=T^2 := by
      rw [hR₂,v.map_add_eq_of_lt_left (hsmall.trans_lt (hTT.trans_eq hmain.symm)),hmain]
    rw [zmZ h₂]
    refine ⟨fun i => ?_,⟨2,hR₂'⟩⟩
    fin_cases i
    · exact hr₀.trans_le (hT.le.trans hTT.le)
    · exact hR₁.trans_le hTT.le
    · exact hR₂'.le
  · have hmin:min m 2=1 := by omega
    have hz₂:m.choose 2=0:=Nat.choose_eq_zero_of_lt (by omega)
    rw [hmin,pow_one]
    refine ⟨fun i => ?_,⟨1,hR₁⟩⟩
    fin_cases i
    · exact hr₀.trans_le hT.le
    · exact hR₁.le
    · rw [hR₂,hz₂,zQq,z1S,zOP]
      exact hsmall
end
end aY5
end
section
namespace aY5
open Polynomial E7
open scoped Polynomial WithZero
noncomputable section
variable {F L:Type} [zrb F] [zrb L]
private theorem b2L (e :F[X] →+* L) (v :zfZ L ℤᵐ⁰)
  {f :F[X]} (B:bjs f) :
  v (e f) = ∏ i,v (e (B.factor i))^B.multiplicity i:= by
 rw [zPw e B.product_eq,zRa,zRa]
 simp only [zkq]
private theorem gEy (j:F →+* L) (a :L) (v :zfZ L ℤᵐ⁰)
    (ha :v a=1) (hj : ∀ x :F,x≠0→v (j x)=1)
    (he :zq4 (zqf j a)) {f :F[X]} (B:bjs f) {N :ℕ} :
    Tq v (OX (N :=N) j f) =
        ∑ i,B.multiplicity i*zbb v ((B.factor i).eval₂ j a) ∧
      Tq v (fun i:Fin 3=>DZ (zqf j a) i.val f) =
        ∑ i,min (B.multiplicity i) 2*KB v ((B.factor i).eval₂ j a) := by
  classical
  let e :=zqf j a
  change _∧Tq v (fun i:Fin 3=>DZ e i.val f) =
    ∑ i,min (B.multiplicity i) 2*KB v (e (B.factor i))
  have hj' (x :F) :v (j x)≤1 := by
    by_cases hx :x=0 <;> simp [hx,hj]
  have hcast' (n:ℕ) (hn: (n:F)≠0) :v (n:L)=1 := by
    simpa only [zGu] using hj (n:F) hn
  have hint (p:F[X]) (i:ℕ) :v (e (z75 i p))≤1 :=
    cMZ j a v ha p i (fun n _=>hj' (p.coeff n))
  have heint (p:F[X]) :v (e p)≤1 := by
    simpa using hint p 0
  constructor
  · rw [cum v (OX (N :=N) j f) (fun i=>hj' (f.coeff i.val))]
    symm
    apply zYF
    intro i _
    have hi:=cb8 v (heint (B.factor i))
    change B.multiplicity i*zbb v (e (B.factor i))=0
    rw [hi,znR]
  · by_cases hz : ∃ r,v (e (B.factor r))<1
    · obtain ⟨r,hr⟩:=hz
      have hu (i:Fin B.count) (hi:i≠r) :v (e (B.factor i))=1 :=
        cMR e v heint (B.coprime r i hi.symm) hr
      have hd:v (e (z75 1 (B.factor r)))=1 := by
        rw [hasseDeriv_one']
        exact cMR e v heint (B.separable r) hr
      let rest := ∏ i∈Finset.univ.erase r,B.factor i^B.multiplicity i
      have hf :f=B.factor r^B.multiplicity r*rest :=
        B.product_eq.trans
          (Finset.mul_prod_erase _ (fun i=>B.factor i^B.multiplicity i)
            (zTc r)).symm
      have hrest:v (e rest)=1 := by
        unfold rest
        rw [zRa,zRa]
        simp only [zkq]
        apply Finset.prod_eq_one
        intro i hi
        rw [hu i (Finset.ne_of_mem_erase hi),one_pow]
      have hne :e (B.factor r)≠0:= by
        intro h
        apply (B.monic r).ne_zero
        exact he (h.trans (zhc e).symm)
      obtain ⟨hmax,hattain⟩:=exI e v (B.factor r) rest (B.multiplicity r)
        (B.positive r) hne hr hd hrest hint
        (hcast' _ (B.first_scalar r)) (fun hm=>hcast' _ (B.second_scalar r hm))
      have hmax_ne : (v (e (B.factor r)))⁻¹^min (B.multiplicity r) 2≠0 :=
        zm1 _ (inv_ne_zero (v.ne_zero_iff.mpr hne))
      rw [show Tq v (fun i:Fin 3=>DZ e i.val f) =
          Tq v (fun i:Fin 3=>DZ e i.val (B.factor r^B.multiplicity r*rest))
          from zPw (fun g=>Tq v (fun i:Fin 3=>DZ e i.val g)) hf,
        dih v _ hmax_ne hmax hattain,
        zpa r (zTc r) (fun i _ hi=> by
          rw [cw4 v (hu i hi).ge,znR])]
      have hinv :1≤(v (e (B.factor r)))⁻¹ :=
        ((one_lt_inv₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr hne))).2 hr).le
      rw [cYN _ _ hinv,WithZero.log_inv,KB]
    · have hu (i:Fin B.count) :v (e (B.factor i))=1 :=
        (heint _).antisymm (zHm fun hi=>hz ⟨i,hi⟩)
      have hf :v (e f)=1 := by simp [b2L e v B,hu]
      rw [cum v _ (fun i=> by
        rw [DZ,v.map_div,hf,div_one]
        exact hint _ _)]
      have hz₀ (i:Fin B.count) :KB v (e (B.factor i))=0 :=
        cw4 v (hu i).ge
      simp [hz₀]
private theorem eff (j:F →+* L) (a :L) (v :zfZ L ℤᵐ⁰)
    (ha :v a=1)
    (hG : ∀ g:F[X],v (g.eval₂ j a)=g.support.sup (fun i=>v (j (g.coeff i))))
    {f :F[X]} (B:bjs f) {N :ℕ} (hN :f.natDegree<N) :
    Tq v (OX (N :=N) j f) =
        ∑ i,B.multiplicity i*zbb v ((B.factor i).eval₂ j a) ∧
      Tq v (fun i:Fin 3=>DZ (zqf j a) i.val f) =
        ∑ i,min (B.multiplicity i) 2*KB v ((B.factor i).eval₂ j a) := by
  let e :=zqf j a
  have hbound (g:F[X]) (n:ℕ) :v (j (g.coeff n))≤v (e g) := by
    by_cases hn:g.coeff n=0
    · simp [hn]
    · change _≤v (g.eval₂ j a)
      rw [hG]
      exact zZi (s :=g.support) (f := fun i=>v (j (g.coeff i))) (mem_support_iff.mpr hn)
  have hfactor (i:Fin B.count) :1≤v (e (B.factor i)) := by
    have hi:=hbound (B.factor i) (B.factor i).natDegree
    simpa [(B.monic i).coeff_natDegree] using hi
  have hf :1≤v (e f) := by
    rw [b2L e v B]
    exact z9l (fun i _=>one_le_pow₀ (hfactor i))
  have hfv :v (e f)≠0:=(zero_lt_one.trans_le hf).ne'
  have hfn :f≠0:= by
    intro h
    exact hfv (by rw [h,zhc,zhc])
  obtain ⟨n,hn,hmax⟩ :=
    f.support.exists_mem_eq_sup (support_nonempty.mpr hfn) (fun i=>v (j (f.coeff i)))
  have hFin:n<N :=(le_natDegree_of_ne_zero (mem_support_iff.mp hn)).trans_lt hN
  constructor
  · rw [dih v (OX (N :=N) j f) hfv (fun i=>hbound f i.val)
        ⟨⟨n,hFin⟩,hmax.symm.trans (hG f).symm⟩,b2L e v B,
      ex6 _ _ (fun i _=>one_le_pow₀ (hfactor i))]
    apply zUo rfl
    intro i _
    exact cYN _ _ (hfactor i)
  · rw [cum v (fun i:Fin 3=>DZ e i.val f) (fun i=> by
      rw [DZ,v.map_div]
      apply (div_le_one₀ (zero_lt_one.trans_le hf)).2
      exact cMZ j a v ha f i.val (fun n _=>hbound f n))]
    have hz (i:Fin B.count) :KB v ((B.factor i).eval₂ j a)=0 :=
      cw4 v (hfactor i)
    simp [hz]
theorem proof :E7.c6:= by
 intro F L _ _ j a f B v N hN ha he hG
 have hjet:F8 (avg (n:=3) j a f) 0 =
     fun i:Fin 3=>DZ (zqf j a) i.val f := by
   funext i
   simp [F8,avg,DZ]
 rw [hjet]
 rcases hG with hj | hG
 · exact gEy j a v ha hj he B
 · exact eff j a v ha hG B hN
end
end aY5
end
section
namespace axh
noncomputable section
open aR jA Polynomial
theorem al5:zq4 qV :=
 zxb ao[X] iP
theorem crY (P:af 3) :
  (zDK qV P).support=P.support :=
 MvPolynomial.support_map_of_injective P al5
private theorem dgj (u:iP) (hu:u≠0) (P:z0R) :
  (znf u*P).support=P.support := by
 ext m
 simp [zuk,z06,hu]
theorem afo (R:z0R) :
    ∃ (d:ao[X]) (Q:af 3),d≠0∧Q.support=R.support ∧
      zDK qV Q=znf (qV d)*R:= by
  classical
  let M:=nonZeroDivisors ao[X]
  let d:=IsLocalization.commonDenom M R.support R.coeff
  let num :=IsLocalization.integerMultiple M R.support R.coeff
  let Q:af 3 := ∑ a : ↥R.support,ztt a.val (num a)
  have hd: (d:ao[X])≠0:=nonZeroDivisors.coe_ne_zero d
  have hi:qV (d:ao[X])≠0:=(zw1 qV al5).mpr hd
  have hQ:zDK qV Q=znf (qV d)*R:= by
    ext m
    simp only [zS3,z06,Q,zqN]
    by_cases hm:m∈R.support
    · let a : ↥R.support :=⟨m,hm⟩
      rw [zpa a (zTc a)]
      · have hn:=IsLocalization.map_integerMultiple M R.support R.coeff a
        change qV (num a)=(d:ao[X])•R.coeff a.val at hn
        rw [zd5] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb:b.val≠m:= fun h=>hba (zkt h)
        simp [z0I,hb]
    · have hz :R.coeff m=0:= by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥R.support,
          (ztt a.val (num a) :af 3).coeff m)=0:= by
        apply zYF
        intro a _
        have ha :a.val≠m:= fun h=>hm (h ▸ a.property)
        simp [z0I,ha]
      rw [hz',hz,zhc,znR]
  exact ⟨d,Q,hd,(crY Q).symm.trans
    (zPw MvPolynomial.support hQ |>.trans (dgj _ hi _)),hQ⟩
theorem aC5 (Q:af 3) (S:ao[X]) :
  zY9 (jW S) (zDK qV Q)=qV (cK Q S) := by
 rw [cK,znM]
 exact (MvPolynomial.eval₂_comp qV (jet S) Q).symm
private theorem b8H (Q:af 3) (S:ao[X]) :
   zDK qV (Z8 Q S) =
     zWk (jW S) (zDK qV Q) := by
 have hc: (zDK (σ:=Fin 3) qV).comp znf =
     MvPolynomial.C.comp qV:= by
   apply zz5
   intro x
   simp
 unfold aR.Z8
 rw [MvPolynomial.eval₂_comp_left]
 change _=zSZ znf
   (fun i=>z9v i+MvPolynomial.C (jW S i)) (zDK qV Q)
 rw [MvPolynomial.eval₂_map,hc]
 congr 1
 funext i
 simp [jW]
theorem c2I (Q:af 3) (S:ao[X]) (m:ℕ) :
  Qu (zDK qV Q) (jW S) m↔wU Q S m:= by
 unfold Qu wU
 rw [← b8H,crY]
theorem c2B {Q:af 3} {R:z0R} {d:ao[X]} (hd:d≠0)
  (hQ:zDK qV Q=znf (qV d)*R)
  (S:ao[X]) {m:ℕ} (hR:Qu R (jW S) m) :wU Q S m:= by
 apply (c2I Q S m).mp
 unfold Qu at hR ⊢
 rw [hQ,zok,show zWk (jW S) (znf (qV d)) =
  znf (qV d) by simp [zWk],
  dgj _ ((zw1 qV al5).mpr hd)]
 exact hR
private theorem dO0 (A:z0R) (y :Fin 3→iP) :
  (zWk y A).coeff 0=zY9 y A:= by
 have h: (MvPolynomial.constantCoeff.comp (zWk y) :z0R →+* iP) =
    MvPolynomial.eval y := by
  apply zXT
  · intro r
    simp [zWk]
  · intro i
    simp [zWk]
 exact RingHom.congr_fun h A
theorem aIJ {A P:z0R} {y :Fin 3→iP} {d:ℕ}
    (hA:zY9 y A≠0) (h:Qu (A*P) y d) :Qu P y d:= by
  classical
  intro a ha
  by_contra! hlt
  let U:=zWk y A
  let V:=zWk y P
  obtain ⟨m,hm,hmin⟩:=V.support.exists_min_image (fun e=>e.degree) ⟨a,ha⟩
  have hsmall:m.degree<d:=lt_of_le_of_lt (hmin a ha) hlt
  have hcoeff : (U*V).coeff m=U.coeff 0*V.coeff m:= by
    rw [zcz]
    apply zi6 (0,m)
    · intro z hz hne
      have hzsum:z.1+z.2=m:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
      have hz₁:z.1≠0:= by
        intro hzero
        apply hne
        exact Prod.ext hzero (by simpa [hzero] using hzsum)
      have hpos :0<z.1.degree :=
        Nat.pos_of_ne_zero (fun hh=>hz₁ ((Finsupp.degree_eq_zero_iff _).mp hh))
      have hsum:z.1.degree+z.2.degree=m.degree := by
        rw [← zrl,hzsum]
      have hzero :V.coeff z.2=0:= by
        by_contra hn
        have hle :=hmin z.2 (MvPolynomial.mem_support_iff.mpr hn)
        omega
      rw [hzero,znR]
    · intro hn
      exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zOP m))).elim
  have hu:U.coeff 0≠0:= by rwa [show U=zWk y A by rfl,dO0]
  have hout:m∈(U*V).support := by
    rw [zuk,hcoeff]
    exact zBS hu (MvPolynomial.mem_support_iff.mp hm)
  have hmem:m∈(zWk y (A*P)).support := by simpa only [zok] using hout
  exact (not_le_of_gt hsmall) (h m hmem)
end
end axh
end
section
namespace axh
noncomputable section
open aR wH Polynomial
open jA (H9)
def c1 :Prop :=
  ∀ R:z0R,R≠0 → ∀ b j τ:ℕ,0<τ →
    R.totalDegree≤b→H9 R≤j →
    ∃ H A P:z0R,
      H≠0∧P≠0∧R=A*P∧A∣H^b ∧
      H.totalDegree≤b/τ∧H9 H≤j/τ ∧
      P.totalDegree≤b∧H9 P≤j∧bRT P τ
end
end axh
end
section
namespace cyO
noncomputable section
open jA (Lower H9)
open MvPolynomial (weightedTotalDegree_mul)
open UniqueFactorizationMonoid
local instance :StrongNormalizationMonoid Lower :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
private theorem aOE (F:z0R) :
  H9 F=zXg zf5 F:= by
 unfold H9 zXg
 simp only [zDM,zs5,z5A]
private theorem dlV (w:Fin 3→ℕ) {F:z0R} (hF:F≠0) (n:ℕ) :
   zXg w (F^n)=n*zXg w F:= by
 induction n with
 | zero=>rw [pow_zero,← MvPolynomial.C_1,MvPolynomial.weightedTotalDegree_C,zero_mul]
 | succ n ih =>
    rw [zVI,weightedTotalDegree_mul w _ _ (zm1 _ hF) hF,ih,Nat.succ_mul]
private theorem dVE {f :z0R} (hf :Prime f) :0<f.totalDegree := by
 by_contra! h
 have he :f=znf (f.coeff 0) :=
  MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (za7 h)
 have hc:f.coeff 0≠0:= fun hz=>hf.ne_zero (by rw [he,hz,zhc])
 exact hf.not_isUnit (he.symm ▸ (isUnit_iff_ne_zero.mpr hc).map znf)
private theorem b2M {R:z0R} {s :Multiset z0R}
    (hs :s≤zGM R) :zGM s.prod=s := by
  calc
    zGM s.prod=s.map normalize :=
      normalizedFactors_prod_eq s fun f hf=>irreducible_of_normalized_factor f
        (zvO hs hf)
    _=s.map id :=Multiset.map_congr rfl fun f hf =>
      normalize_normalized_factor f (zvO hs hf)
    _=s :=Multiset.map_id' s
theorem proof :axh.c1 := by
  classical
  intro R hR b j τ hτ hb hj
  let factors :=zGM R
  let high:=factors.filter (fun f=>τ≤factors.count f)
  let low:=factors.filter (fun f => ¬ τ≤factors.count f)
  let H :=high.dedup.prod
  let A:=high.prod
  obtain ⟨u,hu⟩:=prod_normalizedFactors hR
  let P:=low.prod*(u:z0R)
  have hpart:high+low=factors :=Multiset.filter_add_not _ _
  have hRAP:R=A*P:= by
    change R=high.prod*(low.prod*(u:z0R))
    rw [← ztg,← Multiset.prod_add,hpart]
    exact hu.symm
  have hhigh:high≤factors :=z7n _ _
  have hlow:low≤factors :=z7n _ _
  have hdedup:high.dedup≤factors :=(Multiset.dedup_le _).trans hhigh
  have hH :H≠0:=Multiset.prod_ne_zero fun hz =>
    zero_notMem_normalizedFactors R (zvO hdedup hz)
  have hA:A≠0:=left_ne_zero_of_mul (hRAP ▸ hR)
  have hP:P≠0:=zJ0 (hRAP ▸ hR)
  have hnfH :zGM H=high.dedup:=b2M hdedup
  have hnfA:zGM A=high:=b2M hhigh
  have hnfP:zGM P=low :=
    (Associated.normalizedFactors_eq (show Associated low.prod P from ⟨u,rfl⟩)).symm.trans
      (b2M hlow)
  have hpurchase :H^τ∣A:= by
    rw [zJh (zm1 _ hH) hA,
      normalizedFactors_pow,hnfH,hnfA,zyB]
    intro f
    rw [z5K,zKw]
    by_cases hf :f∈high
    · have ht:τ≤factors.count f :=(Multiset.mem_filter.mp hf).2
      have hc:high.count f=factors.count f :=
        Multiset.count_filter_of_pos (p:= fun g=>τ≤factors.count g) ht
      simpa only [hf,if_true,zqe,hc] using ht
    · simp [hf]
  have hexponent (f :z0R) (hf :f∈factors) :factors.count f≤b:= by
    have hp:=prime_of_normalized_factor f hf
    have hdiv :f^factors.count f∣R:= by
      rw [Multiset.pow_count]
      exact (Multiset.prod_dvd_prod_of_le (z7n _ _)).trans
        (prod_normalizedFactors hR).dvd
    have hdegree :=zJD (1 :Fin 3→ℕ) hdiv hR
    rw [dlV _ hp.ne_zero,zBy,zBy]
      at hdegree
    exact (Nat.le_mul_of_pos_right _ (dVE hp)).trans (hdegree.trans hb)
  have hremoved:A∣H^b:= by
    rw [zJh hA (zm1 _ hH),
      normalizedFactors_pow,hnfH,hnfA,zyB]
    intro f
    rw [z5K,zKw]
    by_cases hf :f∈high
    · simp only [hf,if_true,zqe]
      exact (Multiset.count_le_of_le f hhigh).trans (hexponent f (zvO hhigh hf))
    · simp [hf]
  have hAdiv :A∣R:=⟨P,hRAP⟩
  have hPdiv :P∣R:=⟨A,hRAP.trans (zDE A P)⟩
  have hbudget (w:Fin 3→ℕ) (B:ℕ) (hB:zXg w R≤B) :
      zXg w H≤B/τ:= by
    have hd:=zJD w (hpurchase.trans hAdiv) hR
    rw [dlV w hH,z5A τ] at hd
    exact (Nat.le_div_iff_mul_le hτ).mpr (hd.trans hB)
  refine ⟨H,A,P,hH,hP,hRAP,hremoved,?_,?_,?_,?_,?_⟩
  · simpa only [zBy] using
      (hbudget 1 b (by simpa only [zBy] using hb))
  · simpa only [← aOE] using
      (hbudget zf5 j (by simpa only [← aOE] using hj))
  · exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hPdiv hR).trans hb
  · rw [aOE] at hj ⊢
    exact (zJD zf5 hPdiv hR).trans hj
  · intro f hf hdiv
    have hle :=(zJh
      (zm1 _ hf.ne_zero) hP).mp hdiv
    rw [hf.irreducible.normalizedFactors_pow,hnfP,zyB] at hle
    have hc:=hle (normalize f)
    rw [Multiset.count_replicate_self,Multiset.count_filter] at hc
    split at hc <;> omega
end
end cyO
end
section
namespace dnj
noncomputable section
open cu aBa Polynomial Finset
open scoped BigOperators
private theorem ddi (U:ℕ) :
  zsE FX (z0U (Fin 2) FX U)=triangle U:= by
 rw [z0U,
  Module.finrank_eq_nat_card_basis (zzc FX _),
  Nat.card_coe_set_eq]
 change {e :Fin 2 →₀ ℕ | e.degree≤U}.ncard=triangle U
 rw [Finsupp.ncard_setOf_degree_le]
 simp [triangle,zzd,z5A (U + 2)]
end
end dnj
end
