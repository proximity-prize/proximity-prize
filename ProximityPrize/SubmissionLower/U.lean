import ProximityPrize.SubmissionLower.BH
set_option Elab.async false
open _root_ renaming AddCommGroup → z2F, AdjoinRoot.powerBasis → zY5, AlgEquiv.commutes → zNZ, AlgHom.coe_toRingHom → zlv, AlgHom.congr_fun → zcI, AlgHom.id → zhD, AlgHom.toRingHom_eq_coe → ziQ, Algebra → zZE, Algebra.EssFiniteType → zl5, Algebra.EssFiniteType.comp → zQi, Algebra.EssFiniteType.of_comp → z9q, Algebra.EssFiniteType.of_isLocalization → zrU, Algebra.FiniteType → zUK, Algebra.FormallyUnramified → zRd, Algebra.FormallyUnramified.isSeparable → zeG, Algebra.IsAlgebraic → zjH, Algebra.IsAlgebraic.isAlgebraic → zgs, Algebra.IsAlgebraic.trans → z1q, Algebra.IsIntegral → zVK, Algebra.IsIntegral.adjoin → zGw, Algebra.IsIntegral.isIntegral → zmn, Algebra.IsIntegral.of_finite → zux, Algebra.IsIntegral.trans → znC, Algebra.IsSeparable → zw7, Algebra.TensorProduct.comm → zOQ, Algebra.TensorProduct.comm_tmul → zrc, Algebra.TensorProduct.includeRight → zgi, Algebra.TensorProduct.rightAlgebra → z4w, Algebra.TensorProduct.tensorQuotientEquiv → zTd, Algebra.adjoin → zum, Algebra.adjoin_eq_exists_aeval → zOc, Algebra.algebraMap → z12, Algebra.algebraMapSubmonoid → zTz, Algebra.compHom → zYo, Algebra.finite_of_essFiniteType_of_isAlgebraic → zNf, Algebra.finrank_eq_of_equiv_equiv → znu, Algebra.norm → zXP, Algebra.ofId → zNX, Algebra.self_mem_adjoin_singleton → z4N, Algebra.smul_def → zd5, Algebra.trdeg → zls, Cardinal → zpf, Cardinal.mk_fin → zUc, Cardinal.toNat_toENat → zPK, CharP → zLw, CharP.cast_eq_zero_iff → zX2, CommRing → za6, DFunLike.congr_fun → zmU
open _root_ renaming Disjoint → z1v, DoubleQuot.quotQuotEquivQuotSupₐ → zsn, ENat.toNat_natCast → zzq, Equiv.swap → zFe, FaithfulSMul → znE, FaithfulSMul.algebraMap_injective → zJj, Field → zrb, Field.toIsField → zB1, Fin.castAdd → zVs, Fin.castLE → zQY, Fin.natAdd → zzs, Fin.prod_univ_two → zt9, Fin.sum_univ_four → zmL, Finset → zJe, Finset.induction_on → zcw, Finset.mem_insert_of_mem → zJN, Finset.mem_insert_self → zT5, Finset.mem_union_left → zDk, Finset.mem_union_right → zMj, Finset.mul_sum → zxw, Finset.prod_insert → zqY, Finset.range → z4x, Finset.sum_add_distrib → zfW, Finset.sum_attach → zKD, Finset.sum_congr → zUo, Finset.sum_eq_zero → zYF, Finset.sum_insert → z5O, Finset.sum_le_sum → zQk, Finset.sum_map → z93, Finset.sum_sub_distrib → zQr, Finset.sum_subset → zVG, Finsupp.some_apply → zZ7, FractionRing → zNv, Function.Injective → zq4, Function.Surjective → zpX, Ideal → znc, Ideal.IsIntegral.under_lt_under → zu9, Ideal.IsPrime.comap → zCL, Ideal.Quotient.commRing → z0w, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.factor_surjective → zuo, Ideal.Quotient.factorₐ → z5F, Ideal.Quotient.lift → zP2, Ideal.Quotient.lift_mk → z0R, Ideal.Quotient.liftₐ → zTA, Ideal.Quotient.maximal_of_isField → zqX, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_algebraMap → zOY
open _root_ renaming Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.comap → zK3, Ideal.comap_bot_of_injective → zes, Ideal.comap_comap → zg6, Ideal.comap_isPrime → zG1, Ideal.comap_map_of_bijective → zFA, Ideal.comap_map_of_surjective → zEk, Ideal.eq_top_of_isUnit_mem → zAn, Ideal.exists_ideal_over_prime_of_isIntegral → zuu, Ideal.exists_ltSeries_of_hasGoingUp → z1m, Ideal.height_add_one_le_of_lt_of_isPrime → zSK, Ideal.height_le_ringKrullDim_of_isPrime → ztp, Ideal.isCoprime_iff_sup_eq → zDu, Ideal.isCoprime_of_isMaximal → zoy, Ideal.le_comap_map → zzQ, Ideal.map_le_iff_le_comap → zo0, Ideal.map_map → z0L, Ideal.map_mono → zi2, Ideal.map_pow → zXb, Ideal.map_span → zlN, Ideal.map_sup → zXe, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton → zxV, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.mk_ker → zlC, Ideal.pi_quotient_surjective → z5r, Ideal.quotientEquivAlg → zpY, Ideal.quotientEquivAlgOfEq → z9k, Ideal.quotientMap → z3G, Ideal.quotientMap_mk → z5h, Ideal.span → zye, Ideal.span_insert → zf9, Ideal.span_singleton_le_iff_mem → zvl, Ideal.span_singleton_le_span_singleton → zou, Ideal.span_singleton_pow → zNi, Ideal.subset_span → zCn, Infinite.of_injective → ztd, Int.cast_id → ziL, Int.toNat_natCast → zQf, IntermediateField → zbh, IntermediateField.adjoin → zvb, IsAlgebraic → zxf, IsCoprime → zqs, IsDedekindDomain → zJZ, IsDedekindDomain.HeightOneSpectrum → zZx
open _root_ renaming IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity → zwP, IsDedekindDomain.HeightOneSpectrum.valuation_injective → zPZ, IsDedekindDomain.quotientEquivPiFactors → zsT, IsDedekindDomain.quotientEquivPiFactors_mk → znh, IsDiscreteValuationRing → z8E, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal → zRe, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.div_surjective → zJC, IsFractionRing.finrank_right_eq → zGm, IsFractionRing.injective → zxb, IsFractionRing.lift → zIj, IsFractionRing.lift_algebraMap → zoc, IsFractionRing.map → zJ1, IsFractionRing.of_ringEquiv_left → zwJ, IsFractionRing.ringEquivOfRingEquiv → zDt, IsFractionRing.ringEquivOfRingEquiv_algebraMap → zNB, IsIntegral → zsq, IsIntegralClosure.finite → za2, IsIntegralClosure.isDedekindDomain → zGd, IsLocalRing.ResidueField → zhZ, IsLocalRing.length_restrictScalars → z9y, IsLocalRing.maximalIdeal → zrY, IsLocalRing.residue_surjective → z6A, IsLocalization → zNo, IsLocalization.AtPrime.equivQuotMaximalIdealPow → zYv, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain → zx9, IsLocalization.isAlgebraic → zyQ, IsLocalization.isLocalization_of_algEquiv → zfY, IsLocalization.isPrime_of_isPrime_disjoint → znL, IsLocalization.lift → zvq, IsLocalization.lift_eq → zX4, IsLocalization.lift_injective_iff → zcf, IsLocalization.localization_localization_isLocalization_of_has_all_units → zHS, IsLocalization.map_algebraMap_ne_top_iff_disjoint → z78, IsLocalization.map_eq → zi7, IsLocalization.map_units → z0j, IsLocalization.tensorProductEquivOfMapIncludeRight_tmul → zL5, IsLocalization.under_map_of_isPrime_disjoint → ztT, IsPrincipalIdealRing → z8b, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algHom → zKB, IsScalarTower.of_algebraMap_eq → zsL, IsScalarTower.of_algebraMap_eq' → zD8, IsScalarTower.toAlgHom → zE2, IsTranscendenceBasis.mvPolynomial → z8S, IsUnit → zWB
open _root_ renaming KaehlerDifferential → zAL, KaehlerDifferential.map → zUI, LTSeries → zDY, LinearIndependent → z14, LinearMap.finrank_le_finrank_of_injective → zdv, LinearMap.finrank_le_finrank_of_surjective → zs6, LinearMap.pi → z9H, Localization.AtPrime → zhz, Module.Basis.ofVectorSpaceIndex → z3h, Module.Finite → zAa, Module.Finite.equiv → zZc, Module.Finite.of_surjective → zIU, Module.Free → zVy, Module.Free.ChooseBasisIndex → zKb, Module.finrank → zsE, Module.finrank_baseChange → zXY, Module.finrank_eq_zero_of_subsingleton → z6g, Module.finrank_pi_fintype → z0r, Module.finrank_pos → zRt, Module.finrank_zero_of_subsingleton → zuF, Module.length → zKQ, Module.length_eq_finrank → z1C, Module.length_eq_of_surjective → zAi, Module.length_eq_rank → zqA, Module.rank → z1x, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.C_injective → zbo, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aeval_C → zXr, MvPolynomial.aeval_X → zTw, MvPolynomial.affineHilbertPolynomial → zIV, MvPolynomial.algHom_ext → zpH, MvPolynomial.algebraMap_def → zu8, MvPolynomial.algebraMap_eq → zKm, MvPolynomial.algebraTensorAlgEquiv → zoR, MvPolynomial.algebraTensorAlgEquiv_tmul → zVJ, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.eval₂_eq' → z49, MvPolynomial.finSuccEquiv → z8s, MvPolynomial.finSuccEquiv_X_succ → z07, MvPolynomial.finSuccEquiv_X_zero → zOO, MvPolynomial.finSuccEquiv_apply → zyf, MvPolynomial.induction_on → z5i, MvPolynomial.isLocalization → zEY
open _root_ renaming MvPolynomial.ker_map → zRA, MvPolynomial.map → zDK, MvPolynomial.mapEquiv → zuz, MvPolynomial.mapEquiv_apply → zut, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.map_injective → zNV, MvPolynomial.map_map → z6Y, MvPolynomial.map_surjective → z6h, MvPolynomial.mem_pow_idealOfVars_iff' → z7v, MvPolynomial.mem_restrictBidegree_iff_weightedTotalDegree_le → z3D, MvPolynomial.mul_mem_restrictBidegree → zw3, MvPolynomial.pderiv → zWe, MvPolynomial.pderiv_mul → zGW, MvPolynomial.rename → zHw, MvPolynomial.renameEquiv → zGY, MvPolynomial.renameEquiv_apply → zyk, MvPolynomial.rename_C → zt1, MvPolynomial.rename_X → z6l, MvPolynomial.rename_injective → zLm, MvPolynomial.restrictBidegree → zV7, MvPolynomial.ringHom_ext → zXT, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite → zmx, MvPolynomial.sumAlgEquiv → z3k, MvPolynomial.sumAlgEquiv_X_inl → zwY, MvPolynomial.sumAlgEquiv_X_inr → zoo, MvPolynomial.sumRingEquiv → zm2, MvPolynomial.support_map_subset → z88, MvPolynomial.trdeg_of_isDomain → zUx, MvPolynomial.uniqueAlgEquiv → zpe, MvPolynomial.uniqueAlgEquiv_apply → zJG, MvPolynomial.weightedTotalDegree → zXg, MvPolynomial.weightedTotalDegree_rename_of_injective → z8F, Nat.add_assoc → zVg, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.add_mul → zNE, Nat.card_fin → zJa, Nat.cast_succ → zg0, Nat.cast_zero → zQq, Nat.eq_zero_of_le_zero → za7, Nat.exists_eq_succ_of_ne_zero → zwS, Nat.find → zqr, Nat.find_spec → zWq, Nat.le_of_dvd → zTm, Nat.lt_of_succ_lt → zws, Nat.mul_le_mul_left → zBI
open _root_ renaming Nat.mul_le_mul_right → ztf, Nat.pos_of_ne_zero → zOl, Nat.sub_add_cancel → zxt, Nat.succ_mul → zSX, Nat.zero_le → zD0, Nontrivial → zue, Option → zNO, Option.some → zxU, Option.some_injective → z4p, Or.inl → zMH, Order.krullDim_le_of_strictMono → zol, Pairwise → zUQ, Polynomial → zM1, Polynomial.C → z1z, Polynomial.C_injective → zmy, Polynomial.X → z7y, Polynomial.aeval → zEU, Polynomial.aeval_C → z8q, Polynomial.aeval_X → zw0, Polynomial.aeval_algHom_apply → zTM, Polynomial.aeval_def → zCD, Polynomial.algEquivOfTranscendental → zjm, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.coe_mapRingHom → zKC, Polynomial.coeff_derivative → zMD, Polynomial.coeff_eq_zero_of_natDegree_lt → zQl, Polynomial.coeff_zero → zO6, Polynomial.degree_eq_natDegree → zPS, Polynomial.eval → zng, Polynomial.evalRingHom → zhy, Polynomial.eval_C → zFf, Polynomial.eval_X → zB5, Polynomial.eval_zero → zcG, Polynomial.eval₂ → zmH, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_C → zJU, Polynomial.eval₂_X → zC9, Polynomial.eval₂_eq_sum → zI6, Polynomial.eval₂_map → zem, Polynomial.hom_eval₂ → zly, Polynomial.map → zGG, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.map_injective → zTo, Polynomial.map_ne_zero_iff → zeI, Polynomial.map_surjective → zMr, Polynomial.natDegree_map_eq_of_injective → zt8
open _root_ renaming Polynomial.ringHom_ext → z86, Polynomial.separable_iff_derivative_ne_zero → zKY, Polynomial.sum → zhr, Polynomial.trdeg_of_isDomain → zBA, PrimeSpectrum → zy6, PrimeSpectrum.comap → zRL, RatFunc → ziC, RatFunc.C → ztW, RatFunc.X → zyX, RatFunc.algebraMap_C → zyJ, RatFunc.algebraMap_X → zYR, RatFunc.algebraMap_eq_C → z4W, RatFunc.inftyValuation → zuT, RatFunc.inftyValuation.X_inv → zZm, RatFunc.intDegree → zfy, RatFunc.intDegree_mul → zro, RatFunc.intDegree_polynomial → ztb, RatFunc.num_ne_zero → zl3, RelSeries.inductionOn' → zvN, RelSeries.singleton → zYY, RingEquiv.refl → zqD, RingEquiv.subringCongr → zh4, RingEquiv.symm_apply_apply → zp4, RingHom.comap_ker → zEW, RingHom.comp_apply → zQb, RingHom.comp_assoc → zxS, RingHom.congr_fun → zLs, RingHom.ext → zz4, RingHom.id → zz5, RingHom.injective_iff_ker_eq_bot → zli, RingHom.ker → zdq, RingHom.ker_eq_comap_bot → zPx, RingHom.ker_isPrime → zgL, RingHom.mem_ker → zry, Set.disjoint_left → zM4, Set.image_singleton → zyl, Set.mem_singleton → zT1, Set.range → zxp, Submodule.image_span_subset_span → zEE, Submodule.span → zLD, Submonoid → zdT, Submonoid.mem_comap → zeC, Subsingleton → zOt, Subsingleton.elim → zJA, Subtype.ext → zkt, Sum.inl → zQG, Sum.inr → znU, Transcendental → znN
open _root_ renaming UniqueFactorizationMonoid → zsh, UniqueFactorizationMonoid.factors_eq_normalizedFactors → zy7, Valuation.mem_maximalIdeal_iff → zNC, Valuation.mem_valuationSubring_iff → zbt, Valuation.valuationSubring.integers → z9W, Valuation.valuationSubring_eq_top_iff → zt7, ValuationSubring.eq_of_le_of_ne_top → z7D, ValuationSubring.toSubring → zJ2, WithBot → zUi, WithZero.exp → zx0, WithZero.exp_le_exp → zSP, WithZero.exp_le_one_iff → z9J, WithZero.exp_log → zFB, WithZero.exp_lt_one_iff → zqL, WithZero.exp_ne_zero → zBw, WithZero.exp_nsmul → zh5, WithZero.exp_zero → zva, WithZero.exp_zsmul → zEp, WithZero.log → zx3, WithZero.log_exp → zOL, WithZero.log_le_iff_le_exp → z8p, add_le_add → zZP, add_sub_cancel_right → zY6, add_zero → z0a, baC.finite_quotient → z3E, charP_of_injective_ringHom → zgG, congrArg → zPw, cu.Equation → zS3, exists_finite_inj_algHom_of_fg → z4J, exists_integral_inj_algHom_of_fg → zGH, faithfulSMul_iff_algebraMap_injective → zSO, finSumFinEquiv → ziU, finrank_le_of_span_eq_top → zpS, finrank_quotient_span_eq_natDegree → z35, gT.Ambient → z87, inferInstance → zWv, injective_iff_map_eq_zero → zLn, integralClosure → zwB, isAlgebraic_algebraMap → zSH, isField_of_isIntegral_of_isField' → zJW, isIntegral_algebraMap → z7i, ite_eq_left → zYp, ite_eq_right → zND, le_antisymm → zWs, le_rfl → zs1, lt_of_le_of_ne → zXi, map_add → zrl, map_div₀ → zsN
open _root_ renaming map_mul → zok, map_ne_zero → zyg, map_ne_zero_iff → zw1, map_one → zXs, map_pow → zkq, map_sub → zpO, map_sum → zdo, map_zero → zhc, mem_nonZeroDivisors_iff_ne_zero → zyF, minpoly.irreducible → zy4, minpoly.natDegree_le → z48, minpoly.natDegree_pos → zGQ, mul_assoc → ztg, mul_comm → zDE, mul_ne_zero → zBS, mul_one → zqg, multiplicity → zug, nonZeroDivisors → zgt, nonZeroDivisors.ne_zero → zyw, not_le_of_gt → ziF, one_mul → zkF, one_ne_zero → zOR, pI.weight → zRq, pow_ne_zero → zm1, pow_succ → zVI, ringKrullDim → zqe, ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial → zbi, ringKrullDim_eq_zero_of_field → zZT, ringKrullDim_eq_zero_of_isField → z90, sub_eq_zero → zF3, subsingleton_iff_forall_eq → zAZ, sup_le → zbX, trdeg_add_eq → z5k, trdeg_eq_zero → zBT, zero_add → zOP, zsmul_eq_mul → zK0
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace ac3
noncomputable section
open K1 cu gT pI
open scoped Classical
private theorem ewj
    {B A:Type*} [za6 B] [za6 A] [zZE B A]
    [zVK B A] [znE B A] (l:zDY (zy6 B)) :
    ∃ L:zDY (zy6 A),
      L.length=l.length∧L.last.asIdeal.under B=l.last.asIdeal:= by
  induction l using zvN with
  | singleton q =>
    have :=q.isPrime
    have hle : (⊥ : znc A).under B≤q.asIdeal:= by
      change zK3 (z12 B A) ⊥ ≤ q.asIdeal
      rw [← zPx,
        (zli _).mp (zJj B A)]
      exact bot_le
    obtain ⟨Q,_,hQ,hQq⟩:=zuu
      q.asIdeal (⊥ : znc A) hle
    exact ⟨zYY _ ⟨Q,hQ⟩,rfl,hQq⟩
  | snoc l q hq ih =>
    obtain ⟨L,hlen,hlast⟩:=ih
    have :=q.isPrime
    have hlt:l.last<q:=hq
    have hle :L.last.asIdeal.under B≤q.asIdeal:=hlast.trans_le hlt.le
    obtain ⟨Q,hQL,hQ,hQq⟩:=zuu
      q.asIdeal L.last.asIdeal hle
    have hnext:L.last<(⟨Q,hQ⟩:zy6 A) := by
      refine zXi hQL ?_
      intro heq
      have heq' := zPw (fun x :zy6 A=>x.asIdeal.under B) heq
      exact hlt.ne (PrimeSpectrum.ext_iff.mpr (hlast.symm.trans (heq'.trans hQq)))
    exact ⟨L.snoc ⟨Q,hQ⟩ hnext,by simp [RelSeries.snoc,hlen],by simpa using hQq⟩
private theorem dW4
   {B A:Type*} [za6 B] [za6 A] [zZE B A]
   [zVK B A] [znE B A]
   {d:ℕ} (hdim:zqe B=(d:zUi ℕ∞)) :
   zqe A=(d:zUi ℕ∞) := by
 apply zWs
 · rw [← hdim]
   apply zol (zRL (z12 B A))
   intro a b hab
   exact zu9 (R:=B) (show a.asIdeal<b.asIdeal from hab)
 · obtain ⟨l,hlen⟩:=Order.le_krullDim_iff.mp hdim.ge
   obtain ⟨L,hL,_⟩:=ewj (A:=A) l
   exact Order.le_krullDim_iff.mpr ⟨L,hL.trans hlen⟩
private theorem dW5 {k A:Type*} [zrb k] [za6 A]
   [zZE k A] {d:ℕ}
   (g:z3y (Fin d) k →ₐ[k] A) (hg_inj:zq4 g) (hg_fin:g.Finite) :
   zqe A=(d:zUi ℕ∞) := by
 let B:=z3y (Fin d) k
 let _:zZE B A:=g.toRingHom.toAlgebra
 have :zAa B A:=hg_fin
 have :zVK B A:=zux B A
 have :znE B A:=(zSO B A).mpr hg_inj
 have hdim:zqe B=(d:zUi ℕ∞) := by
   simp [B,zmx,
     zZT]
 exact dW4 (A:=A) hdim
private theorem cKJ {k σ:Type*} [zrb k] [Finite σ]
   (I:znc (z3y σ k)) [I.IsPrime] :
   zqe (z3y σ k ⧸ I) =
     ((zIV I).natDegree :zUi ℕ∞) := by
 obtain ⟨d,g,hg_inj,hg_fin⟩ :=
   z4J k (z3y σ k ⧸ I)
 have hdeg:=MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective
   g hg_fin hg_inj
 rw [zJa] at hdeg
 rw [hdeg]
 exact dW5 g hg_inj hg_fin
theorem bZk {I:znc z87} {P:Jet} (hI:xN I)
  (hP:iJ P∉I) {Q:znc z87} (hQ:Q∈aT1 I P) :
  Q.IsPrime∧zqe (gk Q)=1 := by
 have :=hI.prime
 have hmin:Q∈(I ⊔ zye {iJ P}).minimalPrimes :=
  Ideal.mem_minimalPrimesFinset.mp hQ
 have :=hmin.isPrime
 refine ⟨hmin.isPrime,?_⟩
 have hdim:=cKJ I
 rw [hI.dimension] at hdim
 have hd: (zIV I).natDegree=2 := by
  exact_mod_cast hdim.symm
 have hcut:=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hP hmin
 rw [hd] at hcut
 have hdegree : (zIV Q).natDegree=1 := by omega
 rw [cKJ Q,hdegree,Nat.cast_one]
private def b8K {Q:znc z87} {z :K} {S:zM1 K}
  (h:IZ Q z S) :gk Q →ₐ[FX] FX :=
 zTA Q
  (zIe ![jz z,(jz z)^p,kr S,kr S.derivative])
  (fun _ ha=>RingHom.mem_ker.mp (h ha))
private theorem ezr {Q:znc z87} {z :K} {S:zM1 K}
  (h:IZ Q z S) :
  b8K h (zVv Q (z9v 0))=jz z := by
 change zIe
  ![jz z,(jz z)^p,kr S,kr S.derivative]
    (z9v 0)= _
 simp [zTw]
private theorem cpa {Q:znc z87} [Q.IsPrime] (hQ:aYy Q)
   {z :K} {S:zM1 K} (h:IZ Q z S) :
   z12 FX (gk Q) (jz z) =
     zVv Q (z9v 0) := by
 let x :=zVv Q ((z9v 0) :z87)
 have hx :zsq FX x :=(hQ 0).isIntegral
 apply minpoly.root hx
 have hw:=zPw (b8K h) (minpoly.aeval FX x)
 rw [← zTM,zhc] at hw
 have hvalue :b8K h x=jz z :=ezr h
 rw [hvalue] at hw
 simpa [Polynomial.IsRoot,zCD] using hw
end
end ac3
end
section
namespace ac3
noncomputable section
open K1 cu gT pI
open scoped Classical
def c1 :Prop :=
  ∀ (Q:znc z87),Q.IsPrime→ zqe (gk Q)=1 →
    ¬ aYy Q →
    zAa aQ (rM Q) ∧
    0<zsE aQ (rM Q) ∧
    zAa aQ (as2 Q)
def c2 :Prop :=
  ∀ (s :Shape) (I:znc z87) (P:Jet),
    s.J≤ s.B→xN I→ oU P s→iJ P∉I →
    bod (aOS I P)≤dot (zRq s 0) (pN I)
def c3:Prop :=
  ∀ (s :Shape) (I:znc z87) (P:Jet),
    s.J≤ s.B→xN I→ oU P s→iJ P∉I →
    bDF (aOS I P)≤dot (zRq s 1) (pN I)
def c4 :Prop :=
  ∀ (s :Shape) (I:znc z87) (P:Jet),
    s.J≤ s.B→xN I→ oU P s→iJ P∉I →
    (a2T I P).card≤dot (zRq s 2) (pN I)
end
end ac3
end
section
namespace OH
noncomputable section
open cu gT
open scoped RatFunc
attribute [local instance] Polynomial.algebra
abbrev N8:=z3y (Fin 4) aQ
def Q6:z87 →+* N8 :=
 zDK (z12 FX aQ)
abbrev Cr (I:znc z87) :znc N8 :=
 I.map Q6 ⊔ zye {B4 0 1}
def asi (I:znc z87) :z87 →+* rM I :=
 (zVv (Cr I)).comp Q6
def zL (I:znc z87) (i:Fin 4) :rM I :=
 zVv (Cr I) (z9v i)
abbrev PrincipalCut {A:Type} [za6 A] (f :A) :=
 A ⧸ zye {f}
def FZ (k E :Type) [zrb k] [zrb E] [zZE k E] (f :E) :ℕ:= by
  classical
  exact if znN k f then
    zsE (zvb k ({f} : Set E)) E
  else 0
def aHf (k A:Type) [zrb k] [za6 A] [zZE k A] [ztn A]
    (f :A) :ℕ :=
  FZ k (zNv A) (z12 A (zNv A) f)
def bfe (k A:Type) [zrb k] [za6 A] [zZE k A] [ztn A]
    (y v :A) :ℕ :=
  FZ (ziC k) (ziC (zNv A))
    (ztW (z12 A (zNv A) y) +
      zyX*ztW (z12 A (zNv A) v))
structure ak7 (k A:Type) [zrb k] [za6 A] [zZE k A] where
 order :A→ℕ
 constant : ∀ c:k,order (z12 k A c)=0
 add_le : ∀ a b,order (a+b)≤ max (order a) (order b)
 mul_le : ∀ a b,order (a*b)≤order a+order b
structure cxp (k A:Type) [zrb k] [za6 A] [zZE k A] [ztn A]
  (y v :A) where
 count:ℕ
 place :Fin count→ak7 k A
 QZ:Fin count→ℕ
 degree_eq : ∀ f :A,aHf k A f =
  ∑ q,(place q).order f*QZ q
 line_eq :bfe k A y v =
  ∑ q,max ((place q).order y) ((place q).order v)*QZ q
end
end OH
end
section
set_option backward.isDefEq.respectTransparency false
namespace OH
noncomputable section
open cu gT pI Polynomial
open scoped BigOperators
variable {k A:Type} [zrb k] [za6 A] [zZE k A]
private theorem ak7.zero (d:ak7 k A) :d.order 0=0:= by
 simpa using d.constant (0:k)
private theorem ak7.one (d:ak7 k A) :d.order 1=0:= by
 simpa using d.constant (1 :k)
private theorem ak7.pow_le (d:ak7 k A) (a :A) (n:ℕ) :
   d.order (a^n)≤n*d.order a := by
 induction n with
 | zero=>simp [d.one]
 | succ n ih =>
   rw [zVI,zSX]
   exact (d.mul_le _ _).trans (zlr ih _)
private theorem ak7.sum_le (d:ak7 k A) {ι:Type*}
   (t:zJe ι) (f :ι→A) (N :ℕ) (h : ∀ i∈t,d.order (f i)≤N) :
   d.order (∑ i∈t,f i)≤N := by
 classical
 induction t using zcw with
 | empty=>simp [d.zero]
 | insert i t hi ih =>
   rw [z5O hi]
   exact (d.add_le _ _).trans (max_le
     (h i (zT5 _ _)) (ih fun j hj=>h j (zJN hj)))
private theorem gn1 (I:znc z87) :
    zL I 0 =
      z12 aQ (rM I) (ek 1) -
        z12 aQ (rM I) (ek 0)*zL I 1 := by
  let q:=zVv (Cr I)
  have h:q (B4 0 1)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
    (zs0 (z5J _))
  change q (z9v 0+MvPolynomial.C (ek 0)*z9v 1 -
    znf (ek 1))=0 at h
  rw [zpO,zrl,zok,zF3] at h
  exact eq_sub_of_add_eq h
private theorem gn2 (I:znc z87)
   (d:ak7 aQ (rM I)) :
   d.order (zL I 0)≤d.order (zL I 1) := by
 have hneg:z12 aQ (rM I) (-ek 0)*zL I 1 =
     -(z12 aQ (rM I) (ek 0)*zL I 1) := by
   rw [map_neg,neg_mul]
 rw [gn1,sub_eq_add_neg,← hneg]
 apply (d.add_le _ _).trans
 apply max_le
 · simp [d.constant]
 · exact (d.mul_le _ _).trans_eq (by rw [d.constant,zOP])
private def aXw (I:znc z87) :aZ →+* rM I :=
 zOD
  ((z12 aQ (rM I)).comp (z12 FX aQ))
  ![zL I 0,zL I 1]
private theorem goW (I:znc z87) (P:Jet) :
    asi I (iJ P) =
      P.eval₂ (zqf (aXw I) (zL I 2)) (zL I 3) := by
  have hbase : (asi I).comp znf =
      (z12 aQ (rM I)).comp (z12 FX aQ) := by
    apply zz4
    intro a
    change zVv (Cr I)
        (zDK (z12 FX aQ) (znf a :z87)) =
      zVv (Cr I) (znf (z12 FX aQ a))
    rw [zpw]
  have hx (i:Fin 4) :asi I (z9v i)=zL I i:= by
    change zVv (Cr I)
        (zDK (z12 FX aQ) (z9v i:z87)) =
      zVv (Cr I) (z9v i)
    rw [z7N]
  have hseed : ((asi I).comp oi).comp pZ=aXw I:= by
    apply zXT
    · intro a
      simpa [pZ,oi,aXw] using zLs hbase a
    · intro i
      fin_cases i <;> simp [pZ,oi,aXw,hx]
  have hroot : ((asi I).comp oi).comp A7 =
      zqf (aXw I) (zL I 2) := by
    apply z86
    · intro f
      simpa [A7] using zLs hseed f
    · simp [A7,oi,hx]
  change asi I (P.eval₂ _ _)= _
  rw [zly,← zxS,hroot,hx]
private theorem dM1 (I:znc z87)
   (d:ak7 aQ (rM I)) (g:aZ) {u:ℕ}
   (hg:g.totalDegree≤u) :
   d.order (aXw I g)≤u*d.order (zL I 1) := by
 classical
 change d.order (g.eval₂ _ _)≤_
 rw [z49]
 apply d.sum_le
 intro m hm
 rw [zt9]
 have hm' : m 0+m 1≤u:= by
   have h:=(MvPolynomial.le_totalDegree hm).trans hg
   rwa [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two] at h
 apply (d.mul_le _ _).trans
 simp only [zQb,d.constant,zOP,Matrix.cons_val_zero,Matrix.cons_val_one]
 calc
   _≤d.order (zL I 0^m 0)+d.order (zL I 1^m 1) :=d.mul_le _ _
   _≤ m 0*d.order (zL I 0)+m 1*d.order (zL I 1) :=
     z9f (d.pow_le _ _) (d.pow_le _ _)
   _≤ m 0*d.order (zL I 1)+m 1*d.order (zL I 1) :=
     zlr (zBI _ (gn2 I d)) _
   _≤_:= by simpa only [zNE] using ztf (d.order (zL I 1)) hm'
private theorem ep8 {B J i j a b:ℕ}
    (hJB:J≤B) (hij:i+j≤B) (hj:j≤J) :
    i*a+j*b≤(B-J)*a+J*max a b:= by
  have hi:i≤B - j:= by omega
  have hsub:B - j=(B-J)+(J - j) := by omega
  calc
    i*a+j*b≤(B - j)*a+j*b :=
      zlr (ztf _ hi) _
    _=(B-J)*a+((J - j)*a+j*b) := by rw [hsub,zNE,zVg]
    _≤(B-J)*a+((J - j)*max a b+j*max a b) :=
      z3b (z9f (zBI _ (le_max_left _ _))
        (zBI _ (le_max_right _ _))) _
    _ = _:= by rw [← zNE,zxt hj]
theorem fZu (I:znc z87) (d:ak7 aQ (rM I))
    {s :Shape} {P:Jet} (hJB:s.J≤ s.B) (hcaps :oU P s) :
    d.order (asi I (iJ P)) ≤
      s.U*d.order (zL I 1)+(s.B - s.J)*d.order (zL I 2) +
        s.J*max (d.order (zL I 2)) (d.order (zL I 3)) := by
  let x :=d.order (zL I 1)
  let y :=d.order (zL I 2)
  let v :=d.order (zL I 3)
  rw [goW,zI6,zhr]
  apply d.sum_le
  intro j _
  have hsum:d.order ((P.coeff j).eval₂ (aXw I) (zL I 2) *
      zL I 3^j)≤ s.U*x+(s.B - s.J)*y+s.J*max y v := by
    rw [zI6,zhr,Finset.sum_mul]
    apply d.sum_le
    intro i hi
    obtain ⟨hij,hj,hdeg⟩:=hcaps j i (Polynomial.mem_support_iff.mp hi)
    calc
      _≤(d.order (aXw I ((P.coeff j).coeff i)) +
            d.order (zL I 2^i))+d.order (zL I 3^j) :=
        (d.mul_le _ _).trans (zlr (d.mul_le _ _) _)
      _≤(s.U*x+i*y)+j*v :=
        z9f (z9f (dM1 I d _ hdeg) (d.pow_le _ _))
          (d.pow_le _ _)
      _≤_:= by
        rw [zVg,zVg]
        exact z3b (ep8 hJB hij hj) _
  exact hsum
end
end OH
end
section
namespace OH
noncomputable section
open K1 cu gT pI ac3
open scoped BigOperators Classical Function nonZeroDivisors
def c1 :Prop :=
  ∀ I:znc z87,xN I →
    Cr I ≠ ⊤ ∧ zqe (rM I)=1
def c2 :Prop :=
  ∀ (I:znc z87) [ztn (rM I)],xN I →
    aHf aQ (rM I) (zL I 1)=pN I 0 ∧
    aHf aQ (rM I) (zL I 2)=pN I 1 ∧
    bfe aQ (rM I) (zL I 2) (zL I 3) =
      pN I 2
def c3:Prop :=
  ∀ (ell:ℕ) (k A:Type) [zrb k] [zLw k ell] [za6 A] [zZE k A] [ztn A]
    [zUK k A],zqe A=1 →
    ∀ x y v :A,0<aHf k A x→aHf k A x<ell →
    Nonempty (cxp k A y v)
def c4 :Prop :=
  ∀ (k A:Type) [zrb k] [za6 A] [zZE k A] [ztn A]
    [zUK k A],zqe A=1 →
    ∀ f :A,f≠0 →
    zsE k (PrincipalCut f)≤aHf k A f
def c5:Prop :=
  ∀ Q:znc z87,Q.IsPrime→Cr Q ≠ ⊤ →
    (Cr Q).IsPrime∧(Cr Q).comap Q6= Q
private theorem gn3 {I:znc z87} {P:Jet} {Q:znc z87}
  (hQ:Q∈aT1 I P) :
  Cr I ⊔ zye {Q6 (iJ P)} ≤ Cr Q:= by
 have h:=(Ideal.mem_minimalPrimesFinset.mp hQ).le
 refine zbX (sup_le_sup_right (zi2 (le_sup_left.trans h)) _) ?_
 apply (zvl _).mpr
 exact zKg (z7X _
  (h (zs0 (z5J _))))
private theorem bYt (h5:c5) (I:znc z87) (P:Jet)
    [zAa aQ (PrincipalCut (asi I (iJ P)))] :
    bod (aOS I P) ≤
      zsE aQ (PrincipalCut (asi I (iJ P))) := by
  classical
  let S:=(aOS I P).filter (fun Q=>Cr Q ≠ ⊤)
  let G:S→ znc N8:= fun Q=>Cr Q.val
  let J:znc N8:=Cr I ⊔ zye {Q6 (iJ P)}
  have he :PrincipalCut (asi I (iJ P)) ≃ₐ[aQ] (N8 ⧸ J) := by
    have hm :
        (zye {Q6 (iJ P)}).map (zvR aQ (Cr I)) =
          zye {asi I (iJ P)} := by
      rw [zlN,zyl]
      rfl
    let C (L:znc (rM I)) :=
      (rM I ⧸ L) ≃ₐ[aQ] (N8 ⧸ J)
    exact (zPw C hm).mp (zsn aQ (Cr I)
      (zye {Q6 (iJ P)}))
  have :zAa aQ (N8 ⧸ J) :=
    zIU he.toLinearEquiv.toLinearMap he.surjective
  have hcut (Q:S) :Q.val∈aT1 I P :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp Q.property).1).1
  have hsurv (Q:S) :Cr Q.val ≠ ⊤ := (Finset.mem_filter.mp Q.property).2
  have hprime (Q:S) :Q.val.IsPrime :=(Ideal.mem_minimalPrimesFinset.mp (hcut Q)).isPrime
  have hcomp (Q:S) :J≤G Q:=gn3 (hcut Q)
  let project (Q:S) :=z5F aQ (hcomp Q)
  let : ∀ Q:S,zAa aQ (N8 ⧸ G Q) := fun Q =>
    zIU (project Q).toLinearMap (zuo (hcomp Q))
  let : ∀ Q:S,zVy aQ (N8 ⧸ G Q) := fun _=>zWv
  have hmax (Q:S) : (G Q).IsMaximal:= by
    have : (G Q).IsPrime :=(h5 Q.val (hprime Q) (hsurv Q)).1
    have :zVK aQ (N8 ⧸ G Q) :=
      zux ..
    exact zqX (G Q)
      (zJW (S:=N8 ⧸ G Q) (zB1 aQ))
  have hpairs :zUQ (zqs on G) := by
    intro Q R hne
    have :=hmax Q
    have :=hmax R
    apply zoy
    intro h
    apply hne
    apply zkt
    calc
      Q.val=(G Q).comap Q6:=(h5 Q.val (hprime Q) (hsurv Q)).2.symm
      _=(G R).comap Q6:= by rw [h]
      _=R.val :=(h5 R.val (hprime R) (hsurv R)).2
  let f :=z9H fun Q:S=>(project Q).toLinearMap
  have hf :zpX f := by
    intro a
    obtain ⟨r,hr⟩:=z5r hpairs a
    refine ⟨zVv J r,funext fun Q => ?_⟩
    exact hr Q
  have hdim:=zs6 (f :=f) hf
  rw [z0r] at hdim
  rw [he.toLinearEquiv.finrank_eq]
  have hmass :bod (aOS I P) =
      ∑ Q:S,zsE aQ (N8 ⧸ G Q) := by
    calc
      _ = ∑ Q∈S,zsE aQ (rM Q) := by
        unfold bod
        symm
        apply zVG (Finset.filter_subset ..)
        intro Q hQ hmissing
        have htop:Cr Q = ⊤ := by simpa [S,hQ] using hmissing
        change zsE aQ (N8 ⧸ Cr Q)=0
        rw [htop]
        have :zOt (N8 ⧸ (⊤ : znc N8)) :=
          Ideal.Quotient.subsingleton_iff.mpr rfl
        exact z6g _ _
      _ = _:=(zKD S
        (fun Q=>zsE aQ (rM Q))).symm
  rw [hmass]
  exact hdim
private theorem ea0 (k A:Type) [zrb k] [za6 A]
  [zZE k A] [ztn A] [zUK k A]
  (hdim:zqe A=1) {f :A} (hf :f≠0) :
  zAa k (PrincipalCut f) := by
 apply (Module.finite_iff_krullDimLE_zero k (PrincipalCut f)).mpr
 rw [Ring.krullDimLE_iff,zQq,
  ← ENat.WithBot.add_le_add_one_right_iff,zOP]
 exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
  (mem_nonZeroDivisors_iff_ne_zero.mpr hf)).trans_eq hdim
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :
    ac3.c2 := by
  classical
  intro s I P hJB hI hcaps hP
  obtain ⟨hn,hdim⟩:=h1 I hI
  obtain ⟨hp,hc⟩:=h5 I hI.prime hn
  have : (Cr I).IsPrime :=hp
  have :ztn (rM I) :=
    inferInstanceAs (ztn (N8 ⧸ Cr I))
  let f :=asi I (iJ P)
  have hf :f≠0:= by
    intro h
    apply hP
    rw [← hc]
    change Q6 (iJ P)∈Cr I
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨ha,hy,hz⟩:=h2 I hI
  have :zLw aQ p:=zgG
    ((z12 FX aQ).comp jz).injective p
  obtain ⟨D⟩:=h3 p aQ (rM I) hdim
    (zL I 1) (zL I 2) (zL I 3)
    (by rw [ha]; exact hI.seed_size.1) (by rw [ha]; exact hI.seed_size.2)
  have hlength:=h4 aQ (rM I) hdim f hf
  have :zAa aQ (PrincipalCut f) :=
    ea0 aQ (rM I) hdim hf
  have hpoles :aHf aQ (rM I) f ≤
      s.U*pN I 0+(s.B - s.J)*pN I 1 +
        s.J*pN I 2 := by
    rw [← ha,← hy,← hz,D.degree_eq f,D.degree_eq (zL I 1),
      D.degree_eq (zL I 2),D.line_eq]
    simp only [zxw,← zfW]
    apply zQk
    intro q _
    have hrow:=ztf (D.QZ q)
      (fZu I (D.place q) hJB hcaps)
    simpa only [zNE,Nat.mul_assoc] using hrow
  refine (bYt h5 I P).trans (hlength.trans (hpoles.trans_eq ?_))
  simp [dot,zRq,Fin.sum_univ_succ,zVg]
end
end OH
end
section
namespace WJ
noncomputable section
open cu gT
open MvPolynomial
abbrev yT (k :Type) [zrb k] :=z3y (zNO (Fin 2)) k
abbrev Ez (k :Type) [zrb k] :=zNv (z3y (Fin 2) k)
def ahN (k :Type) [zrb k] (i:Fin 2) :Ez k :=
 z12 (z3y (Fin 2) k) (Ez k) (z9v i)
def Mv :z87 →+* yT aQ :=
  zOD (MvPolynomial.C.comp (z12 FX aQ))
    ![z9v (some 0),z9v (some 1),
      znf (ek 1)-MvPolynomial.C (ek 0)*z9v none,
      z9v none]
def RV (I:znc z87) :znc (yT aQ) :=I.map Mv
abbrev XS (I:znc z87) :=gk (RV I)
def UW (I:znc z87) (i:Fin 4) :gk I :=
 zVv I (z9v i)
def aP9 {k :Type} [zrb k] (D:znc (yT k)) :
    znc (yT (Ez k)) :=
  D.map (zDK (z12 k (Ez k))) ⊔ zye
    {z9v (some 0)+MvPolynomial.C (ahN k 0) *
      z9v (some 1)-MvPolynomial.C (ahN k 1)}
abbrev W1 {k :Type} [zrb k] (D:znc (yT k)) :=
 gk (aP9 D)
abbrev JU (k :Type) [zrb k] :=zNv (zM1 k)
def awP (k :Type) [zrb k] :yT k →+* z3y (Fin 2) (JU k) :=
  zOD (MvPolynomial.C.comp (z12 k (JU k)))
    (fun i=>i.elim
      (znf (z12 (zM1 k) (JU k) z7y)) z9v)
abbrev adm {k :Type} [zrb k] (D:znc (yT k)) :=
 gk (D.map (awP k))
end
end WJ
end
section
set_option backward.isDefEq.respectTransparency false
namespace WJ
noncomputable section
open cu gT pI ac3
open MvPolynomial
private def a8o:aZ →+* yT aQ :=
 (zHw (zxU :Fin 2→zNO (Fin 2))).toRingHom.comp
   (zDK (z12 FX aQ))
private abbrev cpW:yT aQ :=
 znf (ek 1)-MvPolynomial.C (ek 0)*z9v none
private abbrev dez :yT aQ:=z9v none
private theorem gsf (q:zS3) :
   Mv (oi (A7 q))=q.eval₂ a8o cpW:= by
 have hseed : (Mv.comp oi).comp pZ=a8o:= by
   apply zXT
   · intro a
     simp [Mv,oi,pZ,a8o,zQb]
   · intro i
     fin_cases i <;> simp [Mv,oi,pZ,a8o,zQb]
 change (Mv.comp oi) (q.eval₂ pZ (z9v 2))= _
 rw [zly,hseed]
 simp [Mv,oi,zQb]
private abbrev Bidegree (b u:ℕ) :=zV7 (Fin 2) aQ b u
private theorem bQr (x :aQ) {b u:ℕ} : znf x∈Bidegree b u:= by
 rw [z3D]
 simp
private theorem cAv (i:zNO (Fin 2)) :
  z9v i∈Bidegree (i.elim 1 fun _=>0) (i.elim 0 fun _=>1) := by
 rw [mem_restrictBidegree]
 intro m hm
 rw [support_X,Finset.mem_singleton] at hm
 subst m
 cases i <;> simp [Finsupp.some_single_none,Finsupp.some_single_some]
private theorem gsg:cpW∈Bidegree 1 0:= by
 apply (Bidegree 1 0).sub_mem (bQr _)
 exact (zw3 (bQr (b:=0) (u:=0) _) (cAv none) :)
private theorem c4Y {f :yT aQ} {b u:ℕ}
   (hf :f∈Bidegree b u) (i:ℕ) :f^i∈Bidegree (i*b) (i*u) := by
 induction i with
 | zero=>simpa only [pow_zero,Nat.zero_mul,← MvPolynomial.C_1] using
     (bQr (b:=0) (u:=0) 1)
 | succ i ih =>
   rw [zVI,zSX,zSX]
   exact zw3 ih hf
private theorem gnW (a :aZ) :a8o a∈Bidegree 0 a.totalDegree := by
 rw [z3D]
 unfold a8o
 rw [zQb]
 let q:=zDK (z12 FX aQ) a
 change zXg _ (zHw zxU q)≤0 ∧
   zXg _ (zHw zxU q)≤a.totalDegree
 rw [z8F (z4p (Fin 2)),
   z8F (z4p (Fin 2))]
 constructor
 · change zXg (0:Fin 2→ℕ) (zDK (z12 FX aQ) a)≤0
   simp [zXg,Finsupp.weight_apply,Finsupp.sum]
 · change zXg (1 :Fin 2→ℕ) (zDK (z12 FX aQ) a)≤_
   rw [weightedTotalDegree_one]
   exact Finset.sup_mono (z88 _ _)
theorem gsj {P:Jet} {s :Shape} (hcaps :oU P s) :
  Mv (iJ P)∈zV7 (Fin 2) aQ s.B s.U:= by
 classical
 change Mv (P.eval₂ (oi.comp A7) (z9v 3))∈_
 have hV:Mv (z9v 3)=dez := by simp [Mv]
 rw [zly,hV,zI6]
 apply (Bidegree s.B s.U).sum_mem
 intro j _
 simp only [zQb,gsf,zI6,zhr,Finset.sum_mul]
 apply (Bidegree s.B s.U).sum_mem
 intro i hi
 let a :=(P.coeff j).coeff i
 obtain ⟨hB,_,hU⟩:=hcaps j i (Polynomial.mem_support_iff.mp hi)
 have hterm :=zw3
  (zw3 (gnW a) (c4Y gsg i))
  (c4Y (cAv none) j)
 have hsmall:a8o a*cpW^i*dez^j∈Bidegree (i+j) a.totalDegree := by
  simpa using hterm
 exact mem_restrictBidegree_mono hsmall hB hU
theorem drU {I:znc z87} (hI:xN I) :
   ¬ zxf FX (UW I 2) := by
 apply transcendental_iff_injective.mpr
 have h: (zEU (UW I 2) :zM1 FX →ₐ[FX] gk I).toRingHom =
     (zVv I).comp F7:= by
   apply z86
   · intro a
     simp [F7,zQb]
     exact (zOY (R₁:=FX) I a).symm
   · simp [UW,F7,zQb]
 change zq4
   (zEU (UW I 2) :zM1 FX →ₐ[FX] gk I).toRingHom
 rw [h]
 exact hI.ordinate_dominant
private theorem dW9 {k σ:Type} [zrb k]
  (Q:znc (z3y σ k)) [Q.IsPrime]
  (halg : ∀ i,zxf k (zVv Q (z9v i))) :
  zqe (gk Q)=0:= by
 let x (i:σ) :gk Q:=zVv Q (z9v i)
 have heq :zIe x=zvR k Q:= by
  apply zpH
  intro i
  exact zTw x i
 have htop:zum k (zxp x) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval k x,heq,AlgHom.range_eq_top]
  exact zld
 have hi:zjH k (gk Q) := by
  apply Algebra.isAlgebraic_iff.mpr
  rw [← htop,Algebra.isAlgebraic_adjoin_iff]
  rintro _ ⟨i,rfl⟩
  exact halg i
 exact z90
  (zJW (S:=gk Q) (zB1 k))
theorem dO4 {Q:znc z87} [Q.IsPrime]
  (hdim:zqe (gk Q)=1) (hseed :aYy Q) :
  ¬ zxf FX (UW Q 2) ∨ ¬ zxf FX (UW Q 3) := by
 by_contra! h
 have halg (i:Fin 4) :zxf FX (UW Q i) := by
  fin_cases i
  · exact hseed 0
  · exact hseed 1
  · exact h.1
  · exact h.2
 have hzero :zqe (gk Q)=0:=dW9 Q halg
 exact zOR (hdim.symm.trans hzero)
theorem dFu {k R ι:Type} [zrb k] [za6 R] [zZE k R] [Fintype ι]
  (C:znc R) [zAa k (R ⧸ C)] (M:ι→ znc R) (hM : ∀ i,(M i).IsMaximal)
  (hCM : ∀ i,C≤M i) (hDistinct :zq4 M) :
  Fintype.card ι≤zsE k (R ⧸ C) := by
 let project :R ⧸ C →ₗ[k] ((i:ι)→R ⧸ M i) :=
  z9H fun i=>(z5F k (hCM i)).toLinearMap
 have hpair :zUQ (fun i j=>zqs (M i) (M j)) := fun i j hij =>
  Ideal.isCoprime_iff_sup_eq.mpr ((hM i).coprime_of_ne (hM j) (fun h=>hij (hDistinct h)))
 have hsurj:zpX project := by
  intro d
  obtain ⟨r,hr⟩:=z5r hpair d
  exact ⟨zVv C r,funext hr⟩
 let _:=zIU project hsurj
 let includeScalars : (ι→k) →ₗ[k] ((i:ι)→R ⧸ M i) :=
  z9H fun i=>(Algebra.linearMap k (R ⧸ M i)).comp (LinearMap.proj i)
 have hinj:zq4 includeScalars := by
  intro a b hab
  funext i
  have :zue (R ⧸ M i) :=Ideal.Quotient.nontrivial_iff.mpr (hM i).ne_top
  exact (z12 k (R ⧸ M i)).injective (congrFun hab i)
 have hle :=(zdv hinj).trans
  (zs6 hsurj)
 simpa only [Module.finrank_fintype_fun_eq_card] using hle
end
end WJ
end
section
namespace aiM
open gT pI OH
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
abbrev Gd (k A:Type) [zrb k] [za6 A] [zZE k A] (x :A) :=
 letI:zZE k[X] A:=(zEU x :k[X] →ₐ[k] A).toRingHom.toAlgebra
 ziC k ⊗[k[X]] A
abbrev anE (k A:Type) [zrb k] [za6 A] [zZE k A] :=
 ziC k ⊗[k] A
abbrev aaz (I:znc z87) :=anE aQ (rM I)
def aWL (k A:Type) [zrb k] [za6 A] [zZE k A] (y v :A) :
    anE k A :=
  (1 ⊗ₜ[k] y)+(zyX ⊗ₜ[k] v)
abbrev KT (I:znc z87) :aaz I :=
 aWL aQ (rM I) (zL I 2) (zL I 3)
open Algebra.TensorProduct in
def a7u (k A E :Type) [zrb k] [za6 A] [zZE k A]
    [zrb E] [zZE k E] [zZE A E] [zsf k A E] :
    anE k A →ₐ[ziC k] ziC E :=
  lift (zNX _ _) (zE2 k A _) fun _ _=>Commute.all _ _
theorem c6R (k A E :Type) [zrb k] [za6 A] [zZE k A]
  [zrb E] [zZE k E] [zZE A E] [zsf k A E] (r :ziC k) (a :A) :
  a7u k A E (r ⊗ₜ[k] a) =
    z12 (ziC k) (ziC E) r*ztW (z12 A E a) := by
 simp only [a7u,Algebra.TensorProduct.lift_tmul,Algebra.ofId_apply,
  IsScalarTower.toAlgHom_apply,zG3 A E (ziC E),
  z4W]
theorem c6S (k E :Type) [zrb k] [zrb E] [zZE k E] :
  z12 (ziC k) (ziC E) zyX=RatFunc.X:= by
 change zIj (zJj (zM1 k) (ziC E))
  (z12 (zM1 k) (ziC k) z7y)= _
 rw [zoc]
 change z12 (zM1 E) (ziC E) (zGG (z12 k E) z7y)= _
 rw [zSo,zYR]
end
end aiM
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 8
namespace aiM
open scoped Polynomial RatFunc TensorProduct nonZeroDivisors
open IsScalarTower
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra
private abbrev aeJ (R:Type) [za6 R] :=z3y Unit R
private local instance (priority :=high) onePolyToRatFunc (R:Type) [za6 R] [ztn R] :
  zZE (aeJ R) (ziC R) :=
 zYo _ (zpe R Unit).toRingEquiv.toRingHom
private local instance (priority :=high) (R:Type) [za6 R] [ztn R] :
 SMul (aeJ R) (ziC R) :=(onePolyToRatFunc R).toSMul
private theorem cai (R:Type) [za6 R] [ztn R] (a :R) :
  z12 (aeJ R) (ziC R) (znf a)=ztW a := by
 change z12 (zM1 R) (ziC R) (zpe R Unit (znf a))= _
 simp [zJG]
private theorem c2q (R:Type) [za6 R] [ztn R] :
  z12 (aeJ R) (ziC R) (z9v ())=RatFunc.X:= by
 change z12 (zM1 R) (ziC R) (zpe R Unit (z9v ()))= _
 simp [zJG]
private local instance (R:Type) [za6 R] [ztn R] :
  zsf R (aeJ R) (ziC R) :=
 zsL fun a=>(cai R a).symm
private local instance (R:Type) [za6 R] [ztn R] :z0o (aeJ R) (ziC R) :=
 zwJ (zpe R Unit).toRingEquiv fun _=>rfl
private theorem edV (A E :Type) [za6 A] [ztn A]
  [zrb E] [zZE A E] [z0o A E] :
  let:zZE (aeJ A) (ziC E) :=zYo _ (z12 (aeJ A) (aeJ E))
  z0o (aeJ A) (ziC E) := by
 let P:=aeJ A
 let Q:=aeJ E
 let M:zdT P:=(zgt A).map znf
 let:zNo M Q:=zWv
 let:zZE P (ziC E) :=zYo _ (z12 P Q)
 let:=zD8 (R:=P) (S:= Q) (A:=ziC E) rfl
 have hinj:zq4 (z12 P Q) :=
  zNV _ (zxb A E)
 have hm:Q⁰.comap (z12 P Q)=P⁰:= by
  ext x
  simp only [zeC,zyF,zw1 _ hinj]
 change zNo P⁰ (ziC E)
 rw [← hm]
 exact zHS M Q⁰ (ziC E)
  (fun _ hu=>hu.mem_nonZeroDivisors)
theorem fTB (k A E :Type) [zrb k] [za6 A] [ztn A]
    [zZE k A] [zrb E] [zZE A E] [zZE k E] [zsf k A E] [z0o A E]
    (f :anE k A →ₐ[ziC k] ziC E)
    (hf : ∀ a :A,f (1 ⊗ₜ[k] a)=ztW (z12 A E a)) :
    let:zZE (anE k A) (ziC E) :=f.toRingHom.toAlgebra
    z0o (anE k A) (ziC E) := by
  let S:=anE k A
  let N :=ziC E
  let P:=aeJ A
  let R:=aeJ k
  let B:=ziC k
  let:zZE A S:=z4w
  let:zsf k A S:=Algebra.TensorProduct.right_isScalarTower
  let toS:P →ₐ[A] S:=zIe fun _=>z12 B S zyX
  let:zZE P S:=toS.toRingHom.toAlgebra
  let:zsf A P S := .of_algebraMap_eq fun a=>(toS.commutes a).symm
  let:zZE R S:=zYo S (z12 R B)
  let:=zD8 (R:=R) (S:=B) (A:=S) rfl
  let:zsf k P S:=zsL fun c=> by
    rw [zG3 k A S,zG3 k A P,zG3 A P S]
  let:=zD8 (R:=R) (S:=P) (A:=S) <| by
    apply zXT
    · intro c
      rw [zQb,zu8,zpw]
      change z12 B S (z12 R B (znf c)) =
        toS (znf (z12 k A c))
      rw [cai,← z4W,← zG3 k B S]
      change z12 k S c=toS (z12 A P (z12 k A c))
      rw [toS.commutes,← zG3 k A S]
    · intro i
      cases i
      rw [zQb,zu8,z7N]
      change z12 B S (z12 R B (z9v ()))=toS (z9v ())
      rw [c2q,show toS (z9v ())= _ from zTw _ _]
  let:Algebra.IsPushout R P B S :=
    ((Algebra.IsPushout.comp_iff (T:=B) k R A P).mp zWv).symm
  let M:=zTz P (zgt R)
  let:zNo M S :=
    (Algebra.isLocalization_iff_isPushout (zgt R) B).mpr zWv
  let:zZE S N :=f.toRingHom.toAlgebra
  let:zZE P N :=zYo N (z12 P (aeJ E))
  let:z0o P N :=edV A E
  let:=zD8 (R:=P) (S:=S) (A:=N) <| by
    apply zXT
    · intro a
      simp only [zQb]
      change z12 (aeJ E) N (zDK (z12 A E) (znf a)) =
        f (toS (znf a))
      rw [zpw]
      change z12 (aeJ E) N (znf (z12 A E a))=f (toS (znf a))
      rw [cai,show toS (znf a)=1 ⊗ₜ[k] a from toS.commutes a,hf]
    · intro i
      cases i
      simp only [zQb]
      change z12 (aeJ E) N (zDK (z12 A E) (z9v ())) =
        f (toS (z9v ()))
      rw [z7N]
      change z12 (aeJ E) N (z9v ())=f (toS (z9v ()))
      rw [c2q,show toS (z9v ())= _ from zTw _ _,f.commutes,
        c6S]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S N
end
end aiM
end
section
set_option backward.isDefEq.respectTransparency false
namespace WJ
noncomputable section
open K1 cu gT pI ac3
def c1 :Prop :=
  ∀ (I:znc z87) (d:ℕ),I.IsPrime →
    zqe (gk I)=((d+1 :ℕ) :zUi ℕ∞) →
    (¬ zxf FX (UW I 2) ∨ ¬ zxf FX (UW I 3)) →
    (RV I).IsPrime ∧
    zqe (XS I)=(d:zUi ℕ∞) ∧
    (RV I).comap Mv=I
def c2 :Prop :=
  ∀ (I:znc z87),zAa dV (Ik I) →
    zAa (Ez aQ) (W1 (RV I)) ∧
    zsE (Ez aQ) (W1 (RV I))≤pN I 2
def c3:Prop :=
  ∀ (I:znc z87),zAa aQ (Lj I) →
    zAa (JU aQ) (adm (RV I)) ∧
    zsE (JU aQ) (adm (RV I))≤pN I 3
def c4 :Prop :=
  ∀ (k :Type) [zrb k] (q:ℕ) [zLw k q] (D:znc (yT k)) (f :yT k) (u b:ℕ),
    D.IsPrime→ zqe (gk D)=1→f∉D →
    f∈zV7 (Fin 2) k b u →
    zAa (Ez k) (W1 D)→zAa (JU k) (adm D) →
    zsE (Ez k) (W1 D)<q →
    zsE (JU k) (adm D)<q →
    zAa k (gk (D ⊔ zye {f})) ∧
    zsE k (gk (D ⊔ zye {f})) ≤
      u*zsE (Ez k) (W1 D) +
      b*zsE (JU k) (adm D)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :ac3.c4 := by
  classical
  intro s I P _ hI hcaps hP
  obtain ⟨hprime,hdim,hcomap⟩:=h1 I 1 hI.prime hI.dimension (zMH (drU hI))
  let f :=Mv (iJ P)
  let C:=RV I ⊔ zye {f}
  have hf :f∉RV I:= by
    intro h
    apply hP
    rw [← hcomap]
    exact h
  obtain ⟨hseedFinite,hseed⟩:=h2 I hI.bfE
  obtain ⟨hvFinite,hv⟩:=h3 I hI.jet_finite
  have :zLw aQ p:=zgG
    ((z12 FX aQ).comp jz).injective p
  obtain ⟨hfinite,hlength⟩:=h4 aQ p (RV I) f s.U s.B hprime hdim hf
    (gsj hcaps) hseedFinite hvFinite
    (hseed.trans_lt hI.mixed_lt) (hv.trans_lt hI.jet_lt)
  have :zAa aQ (gk C) :=hfinite
  let S:=a2T I P
  let M (Q:S) :=RV Q.val
  have hmem (Q:S) :Q.val∈aT1 I P∧aYy Q.val :=
    Finset.mem_filter.mp Q.property
  have hgeom (Q:S) : (M Q).IsPrime ∧
      zqe (gk (M Q))=0∧(M Q).comap Mv= Q.val := by
    obtain ⟨hp,hd⟩:=bZk hI hP (hmem Q).1
    have :Q.val.IsPrime :=hp
    exact h1 Q.val 0 hp hd (dO4 hd (hmem Q).2)
  have hmax (Q:S) : (M Q).IsMaximal:= by
    obtain ⟨hp,hd,_⟩:=hgeom Q
    have : (M Q).IsPrime :=hp
    have :Ring.KrullDimLE 0 (gk (M Q)) :=
      Ring.krullDimLE_iff.mpr (by rw [hd,zQq])
    exact zqX _ Ring.KrullDimLE.isField_of_isDomain
  have hle (Q:S) :C≤M Q:= by
    have hmin: (I ⊔ zye {iJ P}).IsMinimalPrime Q.val :=
      Ideal.mem_minimalPrimesFinset.mp (hmem Q).1
    apply zbX
    · exact zi2 (le_sup_left.trans hmin.le)
    · have hPQ:iJ P∈Q.val :=hmin.le (zs0 (z5J _))
      exact (zvl _).mpr (z7X Mv hPQ)
  have hinj:zq4 M:= by
    intro Q R h
    apply zkt
    exact (hgeom Q).2.2.symm.trans
      ((zPw (zK3 Mv) h).trans (hgeom R).2.2)
  calc
    S.card=Fintype.card S:=(Fintype.card_coe S).symm
    _≤zsE aQ (gk C) :=dFu C M hmax hle hinj
    _≤ s.U*zsE (Ez aQ) (W1 (RV I)) +
        s.B*zsE (JU aQ) (adm (RV I)) :=hlength
    _≤ s.U*pN I 2+s.B*pN I 3 :=
      z9f (zBI _ hseed) (zBI _ hv)
    _=dot (zRq s 2) (pN I) := by
      simp [dot,zRq,zmL]
end
end WJ
end
section
set_option backward.isDefEq.respectTransparency false
namespace aiM
open OH Polynomial
open scoped Polynomial TensorProduct nonZeroDivisors
open scoped IntermediateField.algebraAdjoinAdjoin
noncomputable section
private theorem eeC
    (k E :Type) [zrb k] [zrb E] [zZE k E] (x :E) :
    let:zZE k[X] E :=(zEU x :k[X] →ₐ[k] E).toRingHom.toAlgebra
    FZ k E x=zsE k[X] E := by
  classical
  let:zZE k[X] E :=(zEU x :k[X] →ₐ[k] E).toRingHom.toAlgebra
  by_cases hx :znN k x
  · rw [FZ,zYp hx]
    let B:=zum k ({x} : Set E)
    let F:=zvb k ({x} : Set E)
    calc
      zsE F E=zsE B E :=zGm B F E
      _=zsE k[X] E := by
        symm
        refine znu
          (zjm k x hx).toRingEquiv (zqD E) ?_
        apply zz4
        intro p
        change ((zjm k x hx) p:E)=zEU x p
        simp
  · rw [FZ,zND hx]
    obtain ⟨p,hp,hpx⟩:=not_not.mp hx
    have hz :z1x k[X] E=0:=rank_eq_zero_iff.mpr fun z =>
      ⟨p,hp,by change zEU x p*z=0; rw [hpx,zero_mul]⟩
    simp [zsE,hz]
theorem b4A
   (k A E :Type) [zrb k] [za6 A] [zZE k A] [zrb E]
   [zZE A E] [zZE k E] [zsf k A E] [z0o A E] (x :A) :
   FZ k E (z12 A E x)=zsE (ziC k) (Gd k A x) := by
 let:zZE k[X] A:=(zEU x :k[X] →ₐ[k] A).toRingHom.toAlgebra
 let:zZE k[X] E :=(zEU (z12 A E x) :k[X] →ₐ[k] E).toRingHom.toAlgebra
 let:zsf k[X] A E :=zsL fun p =>
   aeval_algebraMap_apply E x p
 let G:=Gd k A x
 let:zZE A G:=z4w
 calc
   FZ k E (z12 A E x)=zsE k[X] E :=
     eeC k E _
   _=zsE k[X] A:=(IsFractionRing.finrank_left_eq k[X] A E).symm
   _=zsE k[X] G :=
     (IsLocalizedModule.finrank_eq k[X]⁰ (zE2 k[X] A G).toLinearMap zs1).symm
   _=zsE (ziC k) G:=(zGm k[X] (ziC k) G).symm
end
end aiM
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace aiM
open gT pI OH
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
def c1 :Prop :=
  ∀ I:znc z87,
    zsE (ziC aQ) (Gd aQ (rM I) (zL I 1)) =
      zsE aQ (Y0 I)
def c2 :Prop :=
  ∀ I:znc z87,
    zsE (ziC (ziC aQ))
      (anE (ziC aQ)
        (Gd aQ (rM I) (zL I 2))) =
      zsE dV (ani I)
def c3:Prop :=
  ∀ I:znc z87,
    zsE (ziC (ziC aQ))
      (Gd (ziC aQ) (aaz I) (KT I)) =
      zsE dV (Ik I)
private theorem fTA (k A E :Type) [zrb k] [za6 A] [zZE k A]
  [zrb E] [zZE k E] [zZE A E] [zsf k A E] (y v :A) :
  a7u k A E (aWL k A y v) =
    ztW (z12 A E y)+RatFunc.X*ztW (z12 A E v) := by
 simp only [aWL,zrl,c6R,c6S,
  zXs,zkF]
private theorem efA (k A E :Type) [zrb k] [za6 A] [ztn A]
   [zZE k A] [zrb E] [zZE k E] [zZE A E] [zsf k A E]
   [z0o A E] (y v :A) :
   FZ (ziC k) (ziC E)
     (ztW (z12 A E y)+RatFunc.X*ztW (z12 A E v)) =
   zsE (ziC (ziC k))
     (Gd (ziC k) (anE k A) (aWL k A y v)) := by
 let:zZE (anE k A) (ziC E) :=
   (a7u k A E).toRingHom.toAlgebra
 let:=zKB (a7u k A E)
 let:z0o (anE k A) (ziC E) :=
   fTB k A E (a7u k A E) (fun a=> by
     simp only [c6R,zXs,zkF])
 have h:=b4A (ziC k) (anE k A) (ziC E) (aWL k A y v)
 change FZ (ziC k) (ziC E)
   (a7u k A E (aWL k A y v))= _ at h
 rwa [fTA] at h
private theorem fTC (k A:Type) [zrb k] [za6 A] [zZE k A] :
  zsE (ziC k) (anE k A)=zsE k A :=
 zXY
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :
    OH.c2 := by
  intro I _ _
  let A:=rM I
  let E :=zNv A
  refine ⟨?_,?_,?_⟩
  · exact (b4A aQ A E (zL I 1)).trans (h1 I)
  · exact (b4A aQ A E (zL I 2)).trans
      ((fTC (ziC aQ)
        (Gd aQ A (zL I 2))).symm.trans (h2 I))
  · exact (efA aQ A E (zL I 2) (zL I 3)).trans (h3 I)
end
end aiM
end
section
set_option backward.isDefEq.respectTransparency false
namespace MM
noncomputable section
open gT WJ
open scoped TensorProduct WithZero
abbrev e7 (k :Type) [zrb k] :=zNv (zM1 k)
def Qe (k :Type) [zrb k] :yT k →+* yT (e7 k) :=
 zDK (z12 k (e7 k))
def Z9 {k :Type} [zrb k] (D:znc (yT k)) :
    znc (yT (e7 k)) :=
  D.map (Qe k)
abbrev Cz {k :Type} [zrb k] (D:znc (yT k)) :=
 gk (Z9 D)
abbrev CurveField {k :Type} [zrb k] (D:znc (yT k)) :=
 zNv (Cz D)
def auU {k :Type} [zrb k] (D:znc (yT k)) (f :yT k) :
    Cz D :=
  zVv (Z9 D) (Qe k f)
def an9 {k :Type} [zrb k] (D:znc (yT k)) :
    yT k →+* CurveField D :=
  (z12 (Cz D) (CurveField D)).comp
    ((zVv (Z9 D)).comp (Qe k))
def Je {k :Type} [zrb k] (D:znc (yT k)) (i:zNO (Fin 2)) :
    CurveField D :=
  an9 D (z9v i)
def ajC (k :Type) [zrb k] :e7 k :=
 z12 (zM1 k) (e7 k) z7y
def LX {k :Type} [zrb k] (D:znc (yT k)) :CurveField D :=
  let line :yT (e7 k) :=
    z9v (some 0)+MvPolynomial.C (ajC k)*z9v (some 1)
  z12 (Cz D) (CurveField D) (zVv (Z9 D) line)
def aGs (F K:Type) [zrb F] [zrb K] [zZE F K] (x :K) :Prop :=
  znN F x ∧
    zAa (zvb F {x}) K ∧
    zw7 (zvb F {x}) K
def bbi (F K:Type) [zrb F] [zrb K] [zZE F K] (x :K) (n:ℕ) :Prop :=
  zxf F x∨(znN F x∧zAa (zvb F {x}) K ∧
    zsE (zvb F {x}) K≤n)
structure zZ (F K:Type) [zrb F] [zrb K] [zZE F K] where
 val :Valuation K ℤᵐ⁰
 surj:zpX val
 trivial : ∀ c:F,c≠0→val (z12 F K c)=1
variable {F K:Type} [zrb F] [zrb K] [zZE F K]
instance (w:zZ F K) :zZE F w.val.valuationSubring :=
 ((z12 F K).codRestrict w.val.valuationSubring.toSubring fun c=> by
   change (z12 F K) c∈w.val.valuationSubring
   rw [zbt]
   by_cases hc:c=0
   · simp [hc]
   · rw [w.trivial c hc]).toAlgebra
def QZ (w:zZ F K) :ℕ :=
 zsE F (zhZ w.val.valuationSubring)
def poleOrder (w:zZ F K) (x :K) :ℕ:=(zx3 (w.val x)).toNat
def KB (w:zZ F K) (x :K) :ℕ:=(-WithZero.log (w.val x)).toNat
def af8 (S:zJe (zZ F K)) (x :K) :ℕ :=
 ∑ w∈S,QZ w*poleOrder w x
def aAJ (S:zJe (zZ F K)) (x :K) :ℕ :=
 ∑ w∈S,QZ w*KB w x
end
end MM
end
section
set_option backward.isDefEq.respectTransparency false
namespace bzT
open cu gT pI MvPolynomial
open scoped nonZeroDivisors
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev One (A:Type) [za6 A] :=z3y Unit A
private local instance gRM (A:Type) [za6 A] [ztn A] :
  zZE (One A) (ziC A) :=
 zYo _ (zpe A Unit).toRingEquiv.toRingHom
private local instance gRN (A:Type) [za6 A] [ztn A] :
  z0o (One A) (ziC A) :=
 zwJ (zpe A Unit).toRingEquiv fun _=>rfl
private theorem grb (A:Type) [za6 A] [ztn A] (a :A) :
  z12 (One A) (ziC A) (C a)=ztW a := by
 change z12 (zM1 A) (ziC A) (zpe A Unit (C a))= _
 simp [zJG]
private theorem grc (A:Type) [za6 A] [ztn A] :
  z12 (One A) (ziC A) (z9v ())=RatFunc.X:= by
 change z12 (zM1 A) (ziC A) (zpe A Unit (z9v ()))= _
 simp [zJG]
private abbrev bdC (A E :Type) [za6 A] [zrb E] [zZE A E] :
  zZE (One A) (ziC E) :=
 zYo _ (z12 (One A) (One E))
private theorem cNR (A E :Type) [za6 A] [ztn A]
  [zrb E] [zZE A E] [z0o A E] :
  letI:=bdC A E
  z0o (One A) (ziC E) := by
 let P:=One A
 let Q:=One E
 let M:zdT P:=A⁰.map znf
 let:zNo M Q:=zWv
 let:zZE P (ziC E) :=bdC A E
 let:=zD8 (R:=P) (S:= Q) (A:=ziC E) rfl
 have hinj:zq4 (z12 P Q) :=
  zNV _ (zxb A E)
 have hm:Q⁰.comap (z12 P Q)=P⁰:= by
  ext x
  simp only [zeC,zyF,zw1 _ hinj]
 change zNo P⁰ (ziC E)
 rw [← hm]
 exact zHS M Q⁰ (ziC E)
  (fun _ hu=>hu.mem_nonZeroDivisors)
private theorem bpT (A E :Type) [za6 A] [zrb E] [zZE A E] (a :A) :
  letI:=bdC A E
  z12 (One A) (ziC E) (C a)=ztW (z12 A E a) := by
 change z12 (One E) (ziC E) (zDK (z12 A E) (C a))= _
 rw [zpw,grb]
private theorem cNS (A E :Type) [za6 A] [zrb E] [zZE A E] :
  letI:=bdC A E
  z12 (One A) (ziC E) (z9v ())=RatFunc.X:= by
 change z12 (One E) (ziC E) (zDK (z12 A E) (z9v ()))= _
 rw [z7N,grc]
private abbrev Parameters :=z3y (Fin 4) FX
private abbrev aKG:=One (One aZ)
private abbrev e7:=ziC aQ
private abbrev agF:=ziC e7
private local instance gP7:zZE (One aZ) e7:=bdC aZ aQ
private local instance gP8:z0o (One aZ) e7 :=
 cNR aZ aQ
private local instance gRm:zZE aKG agF :=
 bdC (One aZ) e7
private local instance gRn:z0o aKG agF :=
 cNR (One aZ) e7
private def positions :Fin 4 ≃ Unit ⊕ (Unit ⊕ Fin 2) :=
 Equiv.ofBijective
  ![znU (znU 0),znU (zQG ()),znU (znU 1),zQG ()]
  (by decide)
private def nest:Parameters ≃+* aKG :=
 (zGY FX positions).toRingEquiv.trans
   ((zm2 FX Unit (Unit ⊕ Fin 2)).trans
     (zuz Unit (zm2 FX Unit (Fin 2))))
def coefficients :agF ≃+* dV :=
 zDt nest.symm
private theorem bC0 (p:Parameters) :
   coefficients (z12 aKG agF (nest p)) =
     algebraMap Parameters dV p:= by
 rw [coefficients,zNB,zp4]
theorem cGK (i:Fin 2) :
   coefficients (ztW (ztW (ek i))) =
     kz (![0,2] i) := by
 have h (j:Fin 2) :positions (![0,2] j)=znU (znU j) := by
   fin_cases j <;> rfl
 have hn:nest (z9v (![0,2] i))=C (C (z9v i)) := by
   simp [nest,zyk,h,zut]
 have hp:=bC0 (z9v (![0,2] i))
 rwa [hn,bpT,bpT] at hp
theorem cGL :
  coefficients (ztW zyX)=kz 1 := by
 have hn:nest (z9v 1)=C (z9v ()) := by
  simp [nest,zyk,show positions 1=znU (zQG ()) from rfl,zut]
 have hp:=bC0 (z9v 1)
 rwa [hn,bpT,cNS] at hp
theorem cGJ :
  coefficients zyX=kz 3:= by
 have hn:nest (z9v 3)=z9v () := by
  simp [nest,zyk,show positions 3=zQG () from rfl,zut]
 have hp:=bC0 (z9v 3)
 rwa [hn,cNS] at hp
theorem cGI (x :FX) :
   coefficients (ztW (ztW (z12 FX aQ x))) =
     algebraMap FX dV x := by
 have hn:nest (C x)=C (C (C x)) := by
   simp [nest,zyk,zut]
 have hp:=bC0 (C x)
 rwa [hn,bpT,bpT] at hp
end
end bzT
end
section
set_option backward.isDefEq.respectTransparency false
namespace MM
noncomputable section
open gT WJ
open scoped TensorProduct WithZero
variable {k :Type} [zrb k]
variable {D:znc (yT k)}
def aXP (D:znc (yT k)) :
    (e7 k ⊗[k] gk D) ≃ₐ[e7 k] Cz D:= by
  let B:=e7 k
  let e :B ⊗[k] yT k ≃ₐ[B] yT B:=zoR k B
  let i:yT k →+* B ⊗[k] yT k :=
    (zgi (A:=B) (R:=k)).toRingHom
  have he :e.toAlgHom.toRingHom.comp i= Qe k := by
    apply zz4
    intro p
    change e (1 ⊗ₜ[k] p)=zDK (z12 k B) p
    simpa only [e,one_smul] using zVJ k B 1 p
  refine (zTd (R:=k) B (yT k) B D).trans
    (zpY (D.map i) _ e ?_)
  change Z9 D =(D.map i).map e.toAlgHom.toRingHom
  rw [z0L i e.toAlgHom.toRingHom,he]
  rfl
@[simp] theorem deB (D:znc (yT k)) (f :yT k) :
   aXP D (1 ⊗ₜ[k] zVv D f)=auU D f := by
  unfold aXP
  rw [AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change zVv (Z9 D) (zoR k
   (e7 k) (1 ⊗ₜ[k] f))= _
  rw [zVJ,one_smul]
  rfl
theorem cRU [ztn (Cz D)] {f :yT k}
  (hf :f∉D) :an9 D f≠0:= by
 have hinj:zq4 (zgi (R:=k)
    (A:=e7 k) (B:=gk D)) :=
  Algebra.TensorProduct.includeRight_injective (z12 k (e7 k)).injective
 intro hz
 have hx :auU D f=0:= by
  apply zxb (Cz D) (CurveField D)
  rw [zhc]
  exact hz
 have hy : (1 ⊗ₜ[k] zVv D f :e7 k ⊗[k] gk D)=0 :=
  (aXP D).injective ((deB D f).trans (hx.trans (zhc _).symm))
 exact hf (Ideal.Quotient.eq_zero_iff_mem.mp (hinj (by
  simpa only [Algebra.TensorProduct.includeRight_apply,TensorProduct.tmul_zero] using hy)))
private theorem eao (f :yT k) :
    an9 D f =
      f.eval₂ ((z12 (e7 k) (CurveField D)).comp (z12 k (e7 k)))
        (Je D) := by
  change an9 D f=zOD _ (Je D) f
  congr 1
  apply zXT
  · intro c
    simp only [an9,zQb,zTv,Qe,
      zpw]
    change z12 (Cz D) (CurveField D)
      (z12 (e7 k) (Cz D) (z12 k (e7 k) c))= _
    exact (zG3 (e7 k) (Cz D) (CurveField D) _).symm
  · intro i
    simp only [Je,zrD]
private theorem btL {F K:Type} [zrb F] [zrb K] [zZE F K]
   (w:zZ F K) (x :K) (n:ℕ) :
   poleOrder w x≤n↔w.val x≤zx0 (n:ℤ) := by
 by_cases h:w.val x=0
 · simp [poleOrder,h]
 · rw [← z8p h]
   unfold poleOrder
   omega
theorem eMH {F K:Type} [zrb F] [zrb K] [zZE F K]
  {x :K} (hx :zxf F x) (S:zJe (zZ F K)) :
  af8 S x=0:= by
 have h (w:zZ F K) :poleOrder w x=0:= by
  let O:=w.val.valuationSubring
  let _:zsf F O K:=zD8 rfl
  have hi:zsq O x :=hx.isIntegral.tower_top
  exact za7 <| (btL w x 0).mpr (by
    simpa using ((z9W w.val).isIntegral_iff_v_le_one.mp hi))
 simp [af8,h]
theorem gpz {F K:Type} [zrb F] [zrb K] [zZE F K]
  {q:ℕ} [zLw F q] {x :K} (hx :znN F x)
  [zAa (zvb F {x}) K]
  (hsize :zsE (zvb F {x}) K<q) :
  aGs F K x := by
 let E :=zvb F {x}
 let _:zLw E q:=zgG (z12 F E).injective q
 refine ⟨hx,zWv,⟨fun a => ?_⟩⟩
 have ha :zsq E a :=zmn a
 let p:=minpoly E a
 have hpos :0<p.natDegree :=zGQ ha
 have hlt:p.natDegree<q:=(z48 a).trans_lt hsize
 have hcast: (p.natDegree :E)≠0:= by
  intro hz
  exact (ziF hlt) (zTm hpos ((zX2 E q _).mp hz))
 change p.Separable
 apply (zKY (zy4 ha)).2
 intro hzero
 obtain ⟨n,hn⟩:=zwS hpos.ne'
 have hcoeff :=zPw (fun r :zM1 E=>r.coeff n) hzero
 change p.derivative.coeff n=(0:zM1 E).coeff n at hcoeff
 have hmonic:p.coeff p.natDegree=1 :=(minpoly.monic ha).leadingCoeff
 rw [hn] at hmonic
 rw [zMD,zO6,← zg0,
  ← hn,hmonic,zkF] at hcoeff
 exact hcast hcoeff
theorem c5G {F K:Type} [zrb F] [zrb K] [zZE F K]
   {q:ℕ} [zLw F q] {x :K} {n:ℕ} (h:bbi F K x n) (hn:n<q) :
   zxf F x ∨
     (aGs F K x∧zsE (zvb F {x}) K≤n) := by
 rcases h with halg | ⟨ht,hfinite,hrank⟩
 · exact zMH halg
 · let _:=hfinite
   exact Or.inr ⟨gpz ht (hrank.trans_lt hn),hrank⟩
theorem c5C {F K:Type} [zrb F] [zrb K] [zZE F K]
   {x :K} {n:ℕ} (S:zJe (zZ F K))
   (h:zxf F x ∨
     (aGs F K x∧zsE (zvb F {x}) K≤n))
   (hsep:aGs F K x→af8 S x≤zsE (zvb F {x}) K) :
   af8 S x≤n:= by
 rcases h with halg | ⟨hx,hrank⟩
 · rw [eMH halg]
   exact zD0 _
 · exact (hsep hx).trans hrank
private theorem eMJ (D:znc (yT k)) [ztn (Cz D)]
    {f :yT k} {u b:ℕ} (hf :f∈zV7 (Fin 2) k b u)
    (w:zZ (e7 k) (CurveField D))
    (hw:max (poleOrder w (Je D (some 0))) (poleOrder w (Je D (some 1))) ≤
      poleOrder w (LX D)) :
    poleOrder w (an9 D f) ≤
      u*poleOrder w (LX D)+b*poleOrder w (Je D none) := by
  classical
  let U:=poleOrder w (LX D)
  let B:=poleOrder w (Je D none)
  have hnone :=(btL w (Je D none) B).mp zs1
  have hzero :=(btL w (Je D (some 0)) U).mp ((max_le_iff.mp hw).1)
  have hone :=(btL w (Je D (some 1)) U).mp ((max_le_iff.mp hw).2)
  apply (btL w _ _).mpr
  rw [eao,z49]
  apply w.val.map_sum_le
  intro m hm
  obtain ⟨hb,hu⟩:=MvPolynomial.mem_restrictBidegree.mp hf m hm
  rw [Finsupp.degree_eq_sum,Fin.sum_univ_two,zZ7,zZ7] at hu
  have hc (c:e7 k) :w.val (z12 (e7 k) (CurveField D) c)≤1 := by
    by_cases h:c=0
    · simp [h]
    · rw [w.trivial c h]
  simp only [zQb,Fintype.prod_option,zt9,zok,zkq]
  calc
    _≤1*(zx0 (B:ℤ)^m none *
        (zx0 (U:ℤ)^m (some 0)*zx0 (U:ℤ)^m (some 1))) := by
      gcongr <;> first | exact hc _ | exact zero_le
    _=zx0 (((m (some 0)+m (some 1))*U + m none*B:ℕ) :ℤ) := by
      simp only [zkF,← zh5,← WithZero.exp_add,WithZero.exp_inj,
        Int.natCast_add,Int.natCast_mul,nsmul_eq_mul]
      ring
    _≤_:= by
      rw [zSP]
      exact_mod_cast z9f (ztf U hu) (ztf B hb)
theorem eMI (D:znc (yT k)) [ztn (Cz D)]
    {f :yT k} {u b:ℕ} (hf :f∈zV7 (Fin 2) k b u)
    (S:zJe (zZ (e7 k) (CurveField D)))
    (hw : ∀ w:zZ (e7 k) (CurveField D),
      max (poleOrder w (Je D (some 0))) (poleOrder w (Je D (some 1))) ≤
        poleOrder w (LX D)) :
    af8 S (an9 D f) ≤
      u*af8 S (LX D)+b*af8 S (Je D none) := by
  unfold af8
  rw [zxw,zxw,← zfW]
  apply zQk
  intro w _
  calc
    _≤QZ w *
        (u*poleOrder w (LX D)+b*poleOrder w (Je D none)) :=
      zBI _ (eMJ D hf w (hw w))
    _ = _:= by ring
theorem dSM (D:znc (yT k)) (f :yT k) {n:ℕ}
    (hfinite :zAa (e7 k) (Cz D ⧸ zye {auU D f}))
    (hbound:zsE (e7 k) (Cz D ⧸ zye {auU D f})≤n) :
    zAa k (gk (D ⊔ zye {f})) ∧
      zsE k (gk (D ⊔ zye {f}))≤n:= by
  let F:=e7 k
  let J:znc (yT k) :=D ⊔ zye {f}
  let L:znc (yT F) :=zye {Qe k f}
  have hJ:Z9 J=Z9 D ⊔ L:= by
    simp [Z9,J,L,zXe,zlN]
    rfl
  have hL:L.map (zvR F (Z9 D))=zye {auU D f} := by
    rw [zlN,zyl]
    rfl
  let E : (F ⊗[k] gk J) ≃ₐ[F] (Cz D ⧸ zye {auU D f}) :=
    (aXP J).trans ((z9k F hJ).trans
      ((zsn F (Z9 D) L).symm.trans
        (z9k F hL)))
  let _:=hfinite
  let _:=zIU E.symm.toLinearEquiv.toLinearMap E.symm.surjective
  have hfin:zAa k (gk J) := by
    apply Module.rank_lt_aleph0_iff.mp
    have hr :z1x F (F ⊗[k] gk J)=z1x k (gk J) := by
      simpa only [Cardinal.lift_id] using
        (Module.rank_baseChange (R:=F) (S:=k) (M' := gk J))
    rw [← hr]
    exact Module.rank_lt_aleph0 F (F ⊗[k] gk J)
  exact ⟨hfin,(zXY (R:=F)).symm.trans_le
    (E.toLinearEquiv.finrank_eq.trans_le hbound)⟩
end
end MM
end
section
set_option backward.isDefEq.respectTransparency false
namespace MM
noncomputable section
open gT WJ
def c1 :Prop :=
  ∀ (k :Type) [zrb k] (D:znc (yT k)),
    D.IsPrime→ zqe (gk D)=1 →
      ∃ h:ztn (Cz D),letI:=h
        znN (e7 k) (LX D) ∨
          znN (e7 k) (Je D none)
def c2 :Prop :=
  ∀ (k :Type) [zrb k] (D:znc (yT k)) [ztn (Cz D)],
    zAa (Ez k) (W1 D) →
    bbi (e7 k) (CurveField D) (LX D)
      (zsE (Ez k) (W1 D))
def c3:Prop :=
  ∀ (k :Type) [zrb k] (D:znc (yT k)) [ztn (Cz D)],
    zAa (JU k) (adm D) →
    bbi (e7 k) (CurveField D) (Je D none)
      (zsE (JU k) (adm D))
def c4 :Prop :=
  ∀ (k :Type) [zrb k] (D:znc (yT k)) [ztn (Cz D)],
    D.IsPrime→ zqe (gk D)=1 →
    ∀ w:zZ (e7 k) (CurveField D),
      max (poleOrder w (Je D (some 0))) (poleOrder w (Je D (some 1))) ≤
        poleOrder w (LX D)
def c5:Prop :=
  ∀ (F A:Type) [zrb F] [za6 A] [ztn A] [zZE F A] [zUK F A],
    (∃ t:zNv A,aGs F (zNv A) t) →
    zAa A (zwB A (zNv A)) ∧
      zJZ (zwB A (zNv A))
def c6:Prop :=
  ∀ (F A:Type) [zrb F] [za6 A] [ztn A] [zZE F A] [zUK F A],
    zAa A (zwB A (zNv A)) →
    zJZ (zwB A (zNv A)) →
    ∀ f :A,f≠0 →
      zAa F (A ⧸ zye {f}) ∧
      ∃ S:zJe (zZ F (zNv A)),
        zsE F (A ⧸ zye {f})≤aAJ S (z12 A (zNv A) f)
def c7:Prop :=
  ∀ (F K:Type) [zrb F] [zrb K] [zZE F K],
    (∃ t:K,aGs F K t) →
    ∀ (g:K),g≠0 → ∀ S:zJe (zZ F K),
      ∃ T:zJe (zZ F K),aAJ S g≤af8 T g
def c8:Prop :=
  ∀ (F K:Type) [zrb F] [zrb K] [zZE F K]
    (x :K) (S:zJe (zZ F K)),
    aGs F K x→af8 S x≤zsE (zvb F {x}) K
set_option maxHeartbeats 1000000 in
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (h5:c5) (h6:c6) (h7:c7) (h8:c8) :WJ.c4 := by
  classical
  intro k _ q _ D f u b hprime hdim hf hdeg hsFinite hvFinite hsSize hvSize
  obtain ⟨hDomain,hVary⟩:=h1 k D hprime hdim
  let _:=hDomain
  let F:=e7 k
  let K:=CurveField D
  let A:=Cz D
  let x :=LX D
  let v :=Je D none
  let g:=an9 D f
  let s :=zsE (Ez k) (W1 D)
  let e :=zsE (JU k) (adm D)
  let _:zLw F q:=zgG (z12 k F).injective q
  have hx :bbi F K x s :=h2 k D hsFinite
  have hv :bbi F K v e :=h3 k D hvFinite
  have hs :=c5G (F:=F) (K:=K) hx hsSize
  have he :=c5G (F:=F) (K:=K) hv hvSize
  have hsep : ∃ t:K,aGs F K t:= by
    rcases hVary with ht | ht
    · exact ⟨x,(hs.resolve_left ht).1⟩
    · exact ⟨v,(he.resolve_left ht).1⟩
  have hg:g≠0:=cRU hf
  have hf' : auU D f≠0:= fun h=>hg (by
    change z12 A K (auU D f)=0
    rw [h,zhc])
  obtain ⟨hnorm,hDedekind⟩:=h5 F A hsep
  obtain ⟨hfinite,S,hzeros⟩:=h6 F A hnorm hDedekind (auU D f) hf'
  obtain ⟨T,hpoles⟩:=h7 F K hsep g hg S
  have hsBudget:=c5C (F:=F) (K:=K) T hs (h8 F K x T)
  have heBudget:=c5C (F:=F) (K:=K) T he (h8 F K v T)
  refine dSM D f hfinite ?_
  calc
    zsE F (A ⧸ zye {auU D f})≤aAJ S g:=hzeros
    _≤af8 T g:=hpoles
    _≤u*af8 T x+b*af8 T v :=
      eMI D hdeg T (h4 k D hprime hdim)
    _≤u*s+b*e :=
      z9f (zBI _ hsBudget)
        (zBI _ heBudget)
end
end MM
end
section
set_option maxHeartbeats 800000
namespace czm
noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
private theorem dyQ {F K:Type} [zrb F] [zrb K] [zZE F K]
  {t:K} (ht:MM.aGs F K t) :
  IsTranscendenceBasis F (fun _:Fin 1=>t) := by
 let B:=zum F {t}
 let E :=zvb F {t}
 have :zAa E K:=ht.2.1
 have :zjH B E :=zWv
 have :zjH B K:=z1q B E K
 apply (algebraicIndependent_unique_type_iff.mpr ht.1).isTranscendenceBasis_iff_isAlgebraic.mpr
 rw [Set.range_const]
 exact ‹Algebra.IsAlgebraic B K›
private theorem eE7 (F A:Type) [zrb F] [za6 A] [ztn A]
   [zZE F A] [zUK F A] {t:zNv A}
   (ht:MM.aGs F (zNv A) t) :
   ∃ r :A,zVK (zum F {r}) A:= by
 obtain ⟨n,g,hg,hInt⟩:=zGH F A
 let P:=z3y (Fin n) F
 let:zZE P A:=g.toRingHom.toAlgebra
 let:zsf F P A:=zsL fun c=>(g.commutes c).symm
 let:znE P A:=(zSO P A).mpr hg
 have :zVK P A:=⟨hInt⟩
 have :zjH A (zNv A) :=
   zyQ _ (zgt A)
 have h:=((z8S (Fin n) F).algebraMap_comp
   (S:=P) (A:=A)).algebraMap_comp (A:=zNv A)
 have hc:=h.cardinalMk_eq (dyQ ht)
 have hn:n = 1 := by simpa using hc
 subst n
 let e :F[X] ≃ₐ[F] z3y (Fin 1) F:=(zpe F (Fin 1)).symm
 let r :=g (e z7y)
 refine ⟨r,?_⟩
 let B:=zum F {r}
 let rB:B:=⟨r,z4N F r⟩
 have hEq: (zEU (R:=F) r)=g.comp e.toAlgHom:= by
   ext
   simp [r]
 have hEq' : ((z12 B A).comp (zEU (R:=F) rB).toRingHom) =
     (zEU (R:=F) r).toRingHom:= by
   change (((zNX B A).restrictScalars F).comp (zEU (R:=F) rB)).toRingHom= _
   congr 1
   ext
   simp [rB]
 constructor
 apply RingHom.IsIntegral.tower_top (zEU (R:=F) rB).toRingHom (z12 B A)
 rw [hEq',hEq]
 exact (RingHom.isIntegral_of_surjective e.toRingEquiv.toRingHom e.surjective).trans
   _ _ hInt
private theorem gts {F K:Type} [zrb F] [zrb K] [zZE F K]
   (t:K) [zw7 (zvb F {t}) K] :
   zLD K {D F K t} = ⊤ := by
 let E :=zvb F {t}
 let S:=zLD K {D F K t}
 have hElt (x :K) (hx :x∈E) :D F K x∈S:= by
   induction hx using IntermediateField.adjoin_induction with
   | mem x hx =>
     obtain rfl :=Set.mem_singleton_iff.mp hx
     exact Submodule.subset_span (zT1 _)
   | algebraMap c=>rw [Derivation.map_algebraMap]; exact S.zero_mem
   | add x y _ _ hx hy=>rw [map_add]; exact S.add_mem hx hy
   | inv x _ hx=>rw [Derivation.leibniz_inv]; exact S.smul_mem _ hx
   | mul x y _ _ hx hy =>
     rw [Derivation.leibniz]
     exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)
 let f :=zUI F F E K
 have hm (y :zAL F E) :f y∈S:= by
   change y∈(S.restrictScalars E).comap f
   have hle :zLD E (zxp (D F E))≤(S.restrictScalars E).comap f := by
     apply Submodule.span_le.mpr
     rintro _ ⟨z,rfl⟩
     change f (D F E z)∈S
     rw [show f (D F E z)=D F K (z :K) from map_D F F E K z]
     exact hElt z z.property
   exact hle (by rw [span_range_derivation]; trivial)
 have :=Algebra.FormallyUnramified.of_isSeparable E K
 have hsurj:zpX (mapBaseChange F E K) := by
   rw [← LinearMap.range_eq_top,range_mapBaseChange,LinearMap.ker_eq_top]
   ext x
   exact zJA _ _
 apply top_unique
 intro y hy
 clear hy
 obtain ⟨z,rfl⟩:=hsurj y
 induction z with
 | tmul c v=>rw [mapBaseChange_tmul]; exact S.smul_mem c (hm v)
 | add z w hz hw=>rw [map_add]; exact S.add_mem hz hw
private theorem gpM {F K:Type} [zrb F] [zrb K] [zZE F K]
   [zl5 F K] {t s :K} (hspan:zLD K {D F K t} = ⊤)
   (hs :D F K s≠0) :zw7 (zvb F {s}) K:= by
 let E :=zvb F {s}
 let f :=zUI F E K K
 have hsMem:D F K s∈zLD K {D F K t} := by rw [hspan]; trivial
 obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hsMem
 have hc0:c≠0:= fun h=>hs (by simpa [h] using hc.symm)
 have hfs :f (D F K s)=0:= by
   change zUI F E K K (D F K (z12 E K
     (IntermediateField.AdjoinSimple.gen F s)))=0
   rw [map_D,Algebra.algebraMap_self_apply,Derivation.map_algebraMap]
 have hft:f (D F K t)=0:= by
   have he :=zPw f hc
   rw [map_smul,hfs,smul_eq_zero] at he
   exact he.resolve_left hc0
 have :zOt (zAL E K) := by
   apply zAZ 0 |>.mpr
   intro y
   obtain ⟨x,rfl⟩:=map_surjective F E K y
   have hx :x∈zLD K {D F K t} := by rw [hspan]; trivial
   obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hx
   change f (a•D F K t)=0
   rw [map_smul,hft,smul_zero]
 have :zl5 E K:=z9q F E K
 have :zRd E K:=⟨zWv⟩
 exact zeG E K
private theorem eK1 {F A:Type} [zrb F] [za6 A] [ztn A]
    [zZE F A] (r a :A) [zVK (zum F {r}) A] :
    ∃ m:ℕ,zVK (zum F {r^m-a}) A:= by
  classical
  let R:=zum F {r}
  obtain ⟨p,hp,hroot⟩:=zmn (R:=R) a
  change zEU (R:=R) a p=0 at hroot
  let n:=p.natDegree
  have hn:0<n:= by
    by_contra! h
    have hn0:p.natDegree=0:=za7 h
    have hp1 :p=1 := by
      rw [eq_C_of_natDegree_eq_zero hn0,← hn0,hp.coeff_natDegree,C_1]
    rw [hp1,zXs] at hroot
    exact zOR hroot
  choose q hq using fun i:ℕ=>zOc F r (p.coeff i)
  let m:=(z4x n).sup (fun i=>(q i).natDegree)+1
  let s :=r^m-a
  let B:=zum F {s}
  let sB:B:=⟨s,z4N F s⟩
  let v :B[X] :=z7y ^m - C sB
  let term (i:ℕ) :B[X] :=(q i).map (z12 F B)*v^i
  have hm:m≠0:=Nat.succ_ne_zero _
  have hv :v.Monic:=monic_X_pow_sub_C _ hm
  have hdeg:natDegree v=m:=natDegree_X_pow_sub_C
  have hlt (i:ℕ) (hi:i∈z4x n) : (term i).natDegree< m*n:= by
    have hqi: (q i).natDegree< m:=Nat.lt_succ_of_le (Finset.le_sup (f := fun i=>(q i).natDegree) hi)
    calc
      _≤(q i).natDegree+m*i:= by
        apply (natDegree_mul_le).trans
        rw [natDegree_map,natDegree_pow v,hdeg,Nat.mul_comm i m]
      _< m*(i+1) := by rw [Nat.mul_succ]; omega
      _≤ m*n:=zBI _ (Finset.mem_range.mp hi)
  have hsum: (∑ i∈z4x n,term i).degree<(v^n).degree := by
    have hmn:0< m*n:=Nat.mul_pos (zOl hm) hn
    have hd:=natDegree_sum_le_of_forall_le (z4x n) term
      (n:=m*n - 1) (fun i hi=> by have :=hlt i hi; omega)
    apply lt_of_le_of_lt degree_le_natDegree
    rw [zPS (hv.pow n).ne_zero,natDegree_pow v,hdeg,Nat.mul_comm n m]
    exact_mod_cast (show (∑ i∈z4x n,term i).natDegree< m*n by omega)
  have hInt:zsq B r := by
    refine ⟨v^n + ∑ i∈z4x n,term i,(hv.pow n).add_of_left hsum,?_⟩
    have hvr :zEU (R:=B) r v=a := by simp [v,sB,s]
    have heval (i:ℕ) :zEU (R:=B) r (term i)=z12 R A (p.coeff i)*a^i:= by
      simp only [term,zok,zkq,hvr,aeval_map_algebraMap]
      rw [hq]
      rfl
    change zEU (R:=B) r _=0
    rw [zrl,zkq,hvr,zdo]
    simp_rw [heval]
    rw [p.as_sum_range_C_mul_X_pow,Finset.sum_range_succ] at hroot
    simpa [n,hp.coeff_natDegree,add_comm] using hroot
  let S:=zum B {r}
  have hle :R≤S.restrictScalars F:=Algebra.adjoin_le fun x hx =>
    (Subalgebra.mem_restrictScalars F).2 (Algebra.subset_adjoin hx)
  let:zZE R S:=(Subalgebra.inclusion hle).toAlgebra
  have :zsf R S A:=zsL fun _=>rfl
  have :zVK B S:=zGw
    (fun x hx=>Set.mem_singleton_iff.mp hx ▸ hInt)
  have :zVK S A:=Algebra.IsIntegral.tower_top R
  exact ⟨m,znC S⟩
private theorem eFl (F A:Type) [zrb F] [za6 A] [ztn A]
   [zZE F A] [zUK F A] (s :A) (hs :znN F s)
   [zVK (zum F {s}) A]
   [zw7 (zvb F {z12 A (zNv A) s})
     (zNv A)] :
   zAa A (zwB A (zNv A)) ∧
     zJZ (zwB A (zNv A)) := by
 let K:=zNv A
 let B:=zum F {s}
 let B' := zum F {z12 A K s}
 let E :=zvb F {z12 A K s}
 let C:=zwB A K
 have :z8b B :=
   IsPrincipalIdealRing.of_surjective (zjm F s hs).toRingEquiv
     (zjm F s hs).surjective
 have hFrac:z0o B' E := by
   have :znE B' E :=(zSO B' E).mpr
     (fun x y h=>zkt (zPw (fun z :E=>(z :K)) h))
   apply IsFractionRing.of_field B' E
   intro z
   obtain ⟨x,hx,y,hy,heq⟩:=IntermediateField.mem_adjoin_iff_div.mp z.property
   exact ⟨⟨x,hx⟩,⟨y,hy⟩,zkt heq⟩
 let e :B' ≃+* B:=(Algebra.RingHom.adjoinAlgebraMapEquiv (A:=F) (C:=K) s).symm
 let:zZE B E :=((z12 B' E).comp e.symm.toRingHom).toAlgebra
 let:z0o B E :=
   (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (S:=E) e).mp hFrac
 have :zsf B E K:=zsL fun _=>rfl
 have :zl5 A K:=zrU _ (zgt A)
 have :zl5 F K:=zQi F A K
 have :zl5 E K:=z9q F E K
 have :zjH E K:=zWv
 have :zAa E K:=zNf
 have :IsIntegralClosure C B K:= by
   refine ⟨Subtype.val_injective,?_⟩
   intro x
   rw [← IsIntegralClosure.isIntegral_iff (A:=C) (R:=A) (B:=K)]
   exact ⟨IsIntegral.tower_top (R:=B),isIntegral_trans (R:=B) x⟩
 have :zAa B C:=za2 B E K C
 exact ⟨Module.Finite.of_restrictScalars_finite B A C,zGd B E K C⟩
theorem proof :MM.c5:= by
  intro F A _ _ _ _ _ h
  let K:=zNv A
  obtain ⟨t,ht,hfin,hsep⟩:=h
  let:zw7 (zvb F {t}) K:=hsep
  have :zl5 A K:=zrU _ (zgt A)
  have :zl5 F K:=zQi F A K
  have hspan:=gts (F:=F) t
  have hDt:D F K t≠0:= by
    intro hz
    have :zOt (zAL F K) := by
      apply zAZ 0 |>.mpr
      intro x
      have hx :x∈zLD K {D F K t} := by rw [hspan]; trivial
      simpa [hz] using hx
    have :zRd F K:=⟨zWv⟩
    have :zw7 F K:=zeG F K
    exact ht (zgs t)
  obtain ⟨r,hr⟩:=eE7 F A (t:=t) ⟨ht,hfin,hsep⟩
  have hparam (s :A) (hInt:zVK (zum F {s}) A)
      (hds :D F K (z12 A K s)≠0) :
      zAa A (zwB A K)∧zJZ (zwB A K) := by
    have :=hInt
    have :=gpM hspan hds
    have hs :znN F s := by
      intro hs
      let B:=zum F {s}
      have :zVK F B:=zGw
        (fun x hx=>Set.mem_singleton_iff.mp hx ▸ hs.isIntegral)
      have :zVK F A:=znC B
      have :zjH A K:=zyQ _ (zgt A)
      have :zjH F K:=z1q F A K
      exact ht (zgs t)
    exact eFl F A s hs
  by_cases hdr :D F K (z12 A K r)=0
  · have ha : ∃ a :A,D F K (z12 A K a)≠0:= by
      by_contra! hz
      obtain ⟨x,y,_,heq⟩:=zJC A t
      apply hDt
      rw [← heq,Derivation.leibniz_div,hz,hz]
      simp
    obtain ⟨a,ha⟩:=ha
    have :=hr
    obtain ⟨m,hm⟩:=eK1 (F:=F) r a
    apply hparam _ hm
    rwa [zpO,zkq,zpO,Derivation.leibniz_pow,hdr,smul_zero,smul_zero,
      zero_sub,neg_ne_zero]
  · exact hparam r hr hdr
end
end czm
end
section
namespace ac4
noncomputable section
open cu gT
abbrev CS (k :Type) [zrb k] :=zNv (z3y (Fin 2) k)
def arW (k :Type) [zrb k] (i:Fin 2) :CS k :=
 z12 (z3y (Fin 2) k) (CS k) (z9v i)
def Cl (k :Type) [zrb k] :
    z3y (Fin 4) k →+* z3y (Fin 4) (CS k) :=
  zDK (z12 k (CS k))
abbrev W1 {k :Type} [zrb k] (H :znc (z3y (Fin 4) k)) :=
 gk (H.map (Cl k) ⊔ zye
  {z9v 0+MvPolynomial.C (arW k 0)*z9v 1 -
    znf (arW k 1)})
abbrev adm {k :Type} [zrb k] (H :znc (z3y (Fin 4) k)) :=
 gk (H.map (Cl k) ⊔ zye
  {z9v 3-MvPolynomial.C (arW k 1)})
abbrev aiS:=z3y (Fin 4) aQ
def Hr (I:znc z87) :znc aiS :=
 I.map (Cl FX) ⊔ zye {Pp 2}
def aMp {k :Type} [zrb k] :
    zM1 (z3y (Fin 2) k) →+* z3y (Fin 4) k :=
  zqf
    (zHw (zQY (by decide :2≤4))).toRingHom (z9v 3)
def aJA (P:Jet) :zM1 (z3y (Fin 2) aQ) :=
  P.map (zqf (zDK (z12 FX aQ))
    (znf (ek 1)))
end
end ac4
end
section
set_option backward.isDefEq.respectTransparency false
namespace czj
noncomputable section
open gT WJ MM
private abbrev aZu (k :Type) [zrb k] :=z3y (Fin 2) k
variable {k :Type} [zrb k]
private def b6n (k :Type) [zrb k] :
   aZu k ≃ₐ[k] zM1 (z3y (Fin 1) k) :=
 (zGY k (zFe (0:Fin 2) 1)).trans (z8s k 1)
private def bho (k :Type) [zrb k] :z3y (Fin 1) k →+* e7 k :=
 (z12 (zM1 k) (e7 k)).comp (zpe k (Fin 1)).toRingHom
private def aOw (k :Type) [zrb k] :aZu k →+* zM1 (e7 k) :=
 (zhd (bho k)).comp (b6n k).toRingHom
private theorem ewL (k :Type) [zrb k] :
  zq4 (aOw k) := by
 have hs :zq4 (bho k) := by
  intro p q heq
  apply (zpe k (Fin 1)).injective
  exact zxb (zM1 k) (e7 k) heq
 intro p q heq
 apply (b6n k).injective
 exact zTo _ hs heq
private theorem cX6 :
   aOw k (z9v 0)=z1z (ajC k) := by
 change zGG (bho k)
   (z8s k 1
     (zGY k (zFe (0:Fin 2) 1) (z9v 0)))= _
 rw [zyk,z6l,Equiv.swap_apply_left]
 rw [show (1 :Fin 2)=(0:Fin 1).succ from rfl,z07]
 simp [bho,ajC]
private theorem ewM :
   aOw k (z9v 1)=Polynomial.X:= by
 change zGG (bho k)
   (z8s k 1
     (zGY k (zFe (0:Fin 2) 1) (z9v 1)))= _
 rw [zyk,z6l,Equiv.swap_apply_right,
   zOO,zSo]
private theorem cX5 (a :k) :
  aOw k (znf a)=z1z (z12 k (e7 k) a) := by
 change zGG (bho k) (b6n k (z12 k (aZu k) a))= _
 rw [zNZ,zG3 k (z3y (Fin 1) k)
  (zM1 (z3y (Fin 1) k)),Polynomial.algebraMap_eq,zrL]
 change z1z (z12 (zM1 k) (e7 k)
  ((zpe k (Fin 1)) (z12 k (z3y (Fin 1) k) a)))= _
 rw [zNZ]
 exact zPw z1z (zG3 k (zM1 k) (e7 k) a).symm
private def cpX (k :Type) [zrb k] :zM1 k →+* aZu k :=
 zqf znf (z9v 0)
private theorem ewN (p:zM1 k) :
   aOw k (cpX k p) =
    z1z (z12 (zM1 k) (e7 k) p) := by
 suffices h: (aOw k).comp (cpX k) =
    Polynomial.C.comp (z12 (zM1 k) (e7 k)) by
   exact zmU h p
 apply z86
 · intro a
   change aOw k (zmH znf (z9v 0) (z1z a)) =
    z1z (z12 (zM1 k) (e7 k) (z1z a))
   rw [zJU,cX5]
   exact zPw z1z (zG3 k (zM1 k) (e7 k) a)
 · change aOw k (zmH znf (z9v 0) z7y)= _
   rw [zC9]
   exact cX6
section Curve
variable (D:znc (yT k)) [ztn (Cz D)]
private abbrev sU :=
 zvb (e7 k) {LX D}
private def parameter :sU D :=
 ⟨LX D,IntermediateField.mem_adjoin_simple_self _ _⟩
private def brT:aZu k →+* sU D :=
 (zEU (parameter D)).toRingHom.comp (aOw k)
private theorem ewG (ht:znN (e7 k) (LX D)) :
  zq4 (brT D) := by
 have h:znN (e7 k) (parameter D) := by
  intro ha
  exact ht (ha.algHom (sU D).val)
 exact (transcendental_iff_injective.mp h).comp (ewL k)
private def aos (ht:znN (e7 k) (LX D)) :
  Ez k →+* sU D :=
 zIj (ewG D ht)
private theorem ewH (ht:znN (e7 k) (LX D)) (a :k) :
   aos D ht (z12 k (Ez k) a) =
     z12 (e7 k) (sU D) (z12 k (e7 k) a) := by
 rw [zG3 k (aZu k) (Ez k),zKm]
 simp [aos,brT,cX5]
private theorem cX2 (ht:znN (e7 k) (LX D))
  (p:zM1 k) :
  aos D ht (z12 (aZu k) (Ez k) (cpX k p)) =
    z12 (e7 k) (sU D) (z12 (zM1 k) (e7 k) p) := by
 simp [aos,brT,ewN]
private theorem ewI (ht:znN (e7 k) (LX D)) :
  aos D ht (ahN k 0) =
   z12 (e7 k) (sU D) (ajC k) := by
 simp [aos,ahN,brT,cX6]
private theorem cX1 (ht:znN (e7 k) (LX D)) :
  aos D ht (ahN k 1)=parameter D:= by
 simp [aos,ahN,brT,ewM]
private theorem ewJ (ht:znN (e7 k) (LX D)) :
  zpX (aos D ht) := by
 let f :Ez k →+* CurveField D:=(sU D).val.toRingHom.comp (aos D ht)
 have hbase :zxp (z12 (e7 k) (CurveField D))⊆f.fieldRange := by
  rintro _ ⟨s,rfl⟩
  obtain ⟨p,q,_,rfl⟩:=zJC (zM1 k) s
  rw [zsN]
  apply div_mem
  · exact ⟨_,zPw (sU D).val (cX2 D ht p)⟩
  · exact ⟨_,zPw (sU D).val (cX2 D ht q)⟩
 have hparameter : {LX D} ⊆ (f.fieldRange :Set (CurveField D)) := by
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact ⟨_,zPw (sU D).val (cX1 D ht)⟩
 have h:=IntermediateField.adjoin_le_subfield (e7 k) {LX D} hbase hparameter
 intro x
 obtain ⟨y,hy⟩:=RingHom.mem_fieldRange.mp (h x.property)
 exact ⟨y,(sU D).val.injective hy⟩
private def ewE (ht:znN (e7 k) (LX D)) :
  Ez k ≃+* sU D :=
 RingEquiv.ofBijective (aos D ht) ⟨(aos D ht).injective,ewJ D ht⟩
private def bZh:yT (e7 k) →ₐ[e7 k] CurveField D :=
 (zE2 (e7 k) (Cz D) (CurveField D)).comp
   (zvR (e7 k) (Z9 D))
omit [ztn (Cz D)] in
private theorem dRU :
 bZh D (z9v (some 0) +
  znf (ajC k)*z9v (some 1))=LX D:=rfl
private theorem ea1 {F G M N :Type} [zrb F] [zrb G]
  [z2F M] [z2F N] [Module F M] [Module G N] [zAa F M]
  {σ:F →+* G} (f :M →ₛₗ[σ] N) (hf :zpX f) :
  zAa G N∧zsE G N≤zsE F M:= by
 refine ⟨zIU f hf,?_⟩
 let b:=Module.finBasis F M
 have hspan:zLD G (zxp (f ∘ b)) = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨x,rfl⟩:=hf y
  rw [Set.range_comp]
  exact zEE f _ ⟨x,by rw [b.span_eq]; trivial,rfl⟩
 simpa using zpS hspan
private theorem eaR {L E A R K:Type}
    [zrb L] [zrb E] [za6 A] [zZE L A] [zAa L A]
    [za6 R] [ztn R] [zrb K] [zZE R K] [z0o R K] [zZE E K]
    (e :L ≃+* E) (q:A →+* K)
    (hq : ∀ a,q (z12 L A a)=z12 E K (e a))
    (hR:zxp (z12 R K)⊆q.range) :
    zAa E K∧zsE E K≤zsE L A:= by
  have hsmul (a :L) (x :A) :q (a•x)=e a•q x := by
    rw [zd5,zd5,zok,hq]
  let B:Subalgebra E K :=
    { toSubsemiring :=q.range.toSubsemiring
      algebraMap_mem' := fun a=> by
        obtain ⟨b,rfl⟩:=e.surjective a
        exact ⟨_,hq b⟩ }
  let fB:A →ₛₗ[e.toRingHom] B :=
    { toFun:= fun x=>⟨q x,q.mem_range_self x⟩
      map_add' := fun x y=>zkt (zrl q x y)
      map_smul' := fun a x=>zkt (hsmul a x) }
  have hfB:zpX fB:= by
    rintro ⟨y,hy⟩
    obtain ⟨x,hx⟩:=RingHom.mem_range.mp (show y∈q.range from hy)
    exact ⟨x,zkt hx⟩
  let _:=zIU fB hfB
  let H :=Algebra.IsAlgebraic.toIntermediateField B
  have hsurj:zpX q:= by
    intro y
    obtain ⟨a,b,_,rfl⟩:=zJC R y
    have ha :z12 R K a∈H :=hR ⟨a,rfl⟩
    have hb:z12 R K b∈H :=hR ⟨b,rfl⟩
    have hd:z12 R K a/z12 R K b∈H :=div_mem ha hb
    exact RingHom.mem_range.mp hd
  let f :A →ₛₗ[e.toRingHom] K := { q.toAddMonoidHom with map_smul' := hsmul }
  exact ea1 f hsurj
private theorem goc {K:Type} [zrb K] [zZE (e7 k) K]
    (D:znc (yT k)) (g:yT (e7 k) →ₐ[e7 k] K)
    (coeff :Ez k →+* K) (slopeToLine :e7 k →+* Ez k)
    (hcoeff :coeff.comp slopeToLine=z12 (e7 k) K)
    (hbase :coeff.comp (z12 k (Ez k)) =
      (z12 (e7 k) K).comp (z12 k (e7 k)))
    (hs :coeff (ahN k 0)=z12 (e7 k) K (ajC k))
    (hi:coeff (ahN k 1)=g (z9v (some 0) +
      znf (ajC k)*z9v (some 1)))
    (hD : ∀ p∈D,g (Qe k p)=0) :
    ∃ q:W1 D →+* K,
      (∀ a,q (z12 (Ez k) (W1 D) a)=coeff a) ∧
        zxp g⊆q.range := by
  let φ:yT (Ez k) →+* K :=
    zOD coeff (fun i=>g (z9v i))
  have hφ (p:yT (e7 k)) :
      φ (zDK slopeToLine p)=g p:= by
    change zOD coeff _ (zDK slopeToLine p)= _
    rw [MvPolynomial.eval₂Hom_map_hom,hcoeff]
    exact zmU (by
      apply zXT
      · intro a
        rw [zTv,← zKm]
        exact (g.commutes a).symm
      · intro i
        rw [zrD]
        rfl) p
  have hsource :φ.comp (zDK (z12 k (Ez k))) =
      g.toRingHom.comp (Qe k) := by
    apply zXT
    · intro a
      simp only [zQb,Qe,zpw]
      change zOD coeff _ (znf (z12 k (Ez k) a))= _
      rw [zTv,← zQb,hbase]
      symm
      exact g.commutes _
    · intro i
      simp [φ,Qe]
  have hφX (i:zNO (Fin 2)) :
      φ (z9v i)=g (z9v i) :=
    zrD coeff _ i
  have hφC (a :Ez k) :φ (znf a)=coeff a :=
    zTv coeff _ a
  have hline :φ (z9v (some 0)+MvPolynomial.C (ahN k 0) *
      z9v (some 1)-MvPolynomial.C (ahN k 1))=0:= by
    rw [zpO φ,zrl φ,zok φ,hφX,hφX,hφC,hφC]
    rw [hs,hi,zF3]
    have hc:g (znf (ajC k)) =
        z12 (e7 k) K (ajC k) :=g.commutes _
    rw [zrl g,zok g,hc]
  have hkill:aP9 D ≤zdq φ:= by
    apply zbX
    · apply Ideal.map_le_iff_le_comap.mpr
      intro p hp
      change φ (zDK (z12 k (Ez k)) p)=0
      rw [← zQb,hsource,zQb]
      exact hD p hp
    · apply Ideal.span_le.mpr
      intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      exact hline
  let q:W1 D →+* K:=zP2 (aP9 D) φ
    (fun p hp=>hkill hp)
  refine ⟨q,?_,?_⟩
  · intro a
    change zP2 (aP9 D) φ (fun p hp=>hkill hp)
      (zVv (aP9 D) (znf a))=coeff a
    rw [z0R,hφC]
  · rintro _ ⟨p,rfl⟩
    refine ⟨zVv _ (zDK slopeToLine p),?_⟩
    change zP2 (aP9 D) φ (fun p hp=>hkill hp)
      (zVv _ (zDK slopeToLine p))= _
    rw [z0R,hφ]
set_option maxHeartbeats 1100000 in
private theorem b3a (ht:znN (e7 k) (LX D))
   [zAa (Ez k) (W1 D)] :
   bbi (e7 k) (CurveField D) (LX D)
     (zsE (Ez k) (W1 D)) := by
 refine Or.inr ⟨ht,?_⟩
 let E :=sU D
 let e :Ez k ≃+* E :=ewE D ht
 let coeff :Ez k →+* E :=e.toRingHom
 let slopeToLine :e7 k →+* Ez k :=
   e.symm.toRingHom.comp (z12 (e7 k) E)
 have hcoeff :coeff.comp slopeToLine=z12 (e7 k) E := by
   apply zz4
   intro a
   exact e.apply_symm_apply _
 let coeffK:Ez k →+* CurveField D:=E.val.toRingHom.comp coeff
 have hcoeffK:coeffK.comp slopeToLine=z12 (e7 k) (CurveField D) := by
   change (E.val.toRingHom.comp coeff).comp slopeToLine= _
   rw [zxS,hcoeff]
   apply zz4
   intro a
   exact E.val.commutes a
 have hbase :coeffK.comp (z12 k (Ez k)) =
     (z12 (e7 k) (CurveField D)).comp (z12 k (e7 k)) := by
   apply zz4
   intro a
   change E.val (aos D ht (z12 k (Ez k) a))= _
   rw [ewH,E.val.commutes]
   rfl
 have hs :coeffK (ahN k 0)=z12 (e7 k) (CurveField D) (ajC k) := by
   change E.val (aos D ht (ahN k 0))= _
   rw [ewI,E.val.commutes]
 have hi:coeffK (ahN k 1)=LX D:= by
   change E.val (aos D ht (ahN k 1))= _
   rw [cX1]
   rfl
 have hD (p:yT k) (hp:p∈D) :bZh D (Qe k p)=0:= by
   have hp' : Qe k p∈Z9 D:=z7X _ hp
   change z12 (Cz D) (CurveField D)
     (zVv (Z9 D) (Qe k p))=0
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp']
   exact zhc (z12 (Cz D) (CurveField D))
 obtain ⟨q,hq,hqR⟩:=goc D (bZh D) coeffK slopeToLine
   hcoeffK hbase hs (hi.trans (dRU D).symm) hD
 refine eaR (R:=Cz D) e q hq ?_
 rintro _ ⟨a,rfl⟩
 obtain ⟨p,rfl⟩:=zld a
 exact hqR ⟨p,rfl⟩
theorem proof :MM.c2 := by
 classical
 intro k _ D _ hfinite
 by_cases h:zxf (e7 k) (LX D)
 · exact zMH h
 · let _:=hfinite
   exact b3a D h
end Curve
end
end czj
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace ac4
noncomputable section
open cu gT pI MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Lg:=z3y (Fin 4) aZ
private def CV:z87 →+* Lg :=
 zDK znf
private def bJZ:Lg :=
 z9v 2 - znf (z9v 1)
private def aum (Q:znc z87) :znc Lg :=
 Q.map CV ⊔ zye {bJZ}
private abbrev Ek :zdT Lg :=
 aZ⁰.map (znf (σ:=Fin 4))
private def pD (Q:znc z87) :aZ →+* zM1 (gk Q) :=
 (zhd ((zVv Q).comp F7)).comp
   ((zhd (zpe FX (Fin 1)).toRingHom).comp
     (z8s FX 1).toRingHom)
private theorem c3w (Q:znc z87) :
   zq4 (pD Q) ↔
     zq4 ((zVv Q).comp F7) := by
 let e :=zpe FX (Fin 1)
 let t:=z8s FX 1
 let f :=(zVv Q).comp F7
 change zq4
   (zGG f ∘ (zGG e.toRingHom ∘ t))↔zq4 f
 rw [← Polynomial.map_injective_iff]
 exact ⟨fun h=>h.of_comp_right ((zMr _ e.surjective).comp t.surjective),
   fun h=>h.comp ((zTo _ e.injective).comp t.injective)⟩
private theorem btq (Q:znc z87) (a :FX) :
  pD Q (znf a) =
   z1z (zVv Q (znf a)) := by
 simp [pD,zyf,zpe,
  F7]
private theorem cbh (Q:znc z87) :
  pD Q (z9v 0)=Polynomial.X:= by
 simp [pD,zOO]
private theorem bKf (Q:znc z87) :
   pD Q (z9v 1) =
     z1z (zVv Q (z9v 2)) := by
 let e :=zpe FX (Fin 1)
 let f :=(zVv Q).comp F7
 change zGG f (zGG e.toRingHom
   ((z8s FX 1) (z9v ((0:Fin 1).succ))))= _
 rw [z07,zrL,zrL]
 have he :e (z9v 0)=Polynomial.X:= by
   change MvPolynomial.eval₂ z1z (fun _:Fin 1=>z7y) (z9v 0)= _
   rw [MvPolynomial.eval₂_X]
 change z1z (f (e (z9v 0)))= _
 rw [he]
 simp [f,F7]
private def wW (Q:znc z87) :Lg →+* zM1 (gk Q) :=
 zOD (S₁:=zM1 (gk Q)) (pD Q)
  fun i=>z1z (zVv Q (z9v i))
private theorem ax8 (Q:znc z87) :
   (wW Q).comp CV=Polynomial.C.comp (zVv Q) := by
 apply zXT
 · intro a
   simp only [zQb,wW,CV,zpw,
     zTv,btq]
 · intro i
   simp [wW,CV]
private theorem bb3 (Q:znc z87) :
    aum Q=zdq (wW Q) := by
  let D:=aum Q
  let q:=zVv (R:=Lg) D
  have hD:D ≤zdq (wW Q) := by
    apply zbX
    · rw [zo0]
      intro a ha
      change wW Q (CV a)=0
      have he :=zLs (ax8 Q) a
      rw [zQb,zQb,Ideal.Quotient.eq_zero_iff_mem.mpr ha,
        zhc] at he
      exact he
    · apply (zvl _).mpr
      apply RingHom.mem_ker.mpr
      simp [bJZ,wW,bKf]
  let u:gk Q →+* Lg ⧸ D :=
    zP2 Q (q.comp CV)
      (fun a ha=>Ideal.Quotient.eq_zero_iff_mem.mpr
        (zKg (z7X CV ha)))
  let v :zM1 (gk Q) →+* Lg ⧸ D :=
    zqf u (q (znf (z9v 0)))
  have hrel :q (z9v 2)=q (znf (z9v 1)) := by
    apply sub_eq_zero.mp
    rw [← zpO]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (zs0 (zCn (zT1 _)))
  have he :v.comp (wW Q)=q:= by
    apply zXT
    · have hC: (v.comp (wW Q)).comp znf=q.comp MvPolynomial.C:= by
        apply zXT
        · intro a
          simp only [zQb,wW,zTv,btq,
            v,z4Q,zJU,u,z0R,CV,
            zpw]
        · intro i
          simp only [zQb,wW,zTv]
          fin_cases i
          · change v (pD Q (z9v 0))=q (znf (z9v 0))
            simp [cbh,v]
          · change v (pD Q (z9v 1))=q (znf (z9v 1))
            simp only [bKf,v,z4Q,zJU,u,
              z0R,zQb,CV,z7N]
            exact hrel
      exact zLs hC
    · intro i
      simp only [zQb,wW,zrD,v,
        z4Q,zJU,u,z0R,
        CV,z7N]
  refine zWs hD fun a ha=>Ideal.Quotient.eq_zero_iff_mem.mp ?_
  have hv :=zLs he a
  rw [zQb,RingHom.mem_ker.mp ha,zhc] at hv
  exact hv.symm
private theorem bfm :
   (z12 Lg aiS).comp CV=Cl FX:= by
 change (zDK (z12 aZ aQ)).comp CV=Cl FX
 apply zXT
 · intro a
   simp only [zQb,CV,Cl,zpw]
   rfl
 · intro i
   simp only [zQb,CV,Cl,z7N]
private theorem bse (Q:znc z87) :
   (aum Q).map (z12 Lg aiS)=Hr Q:= by
 rw [aum,zXe,z0L,bfm,
   zlN,zyl]
 change Q.map (Cl FX) ⊔
   zye {zDK (z12 aZ aQ) bJZ} =
     Q.map (Cl FX) ⊔ zye {Pp 2}
 simp only [bJZ,zpO,z7N,zpw,Pp,ek]
theorem btg (Q:znc z87) (hp:Q.IsPrime) :
    (zq4 ((zVv Q).comp F7) →
      (Hr Q).IsPrime∧(Hr Q).comap (Cl FX)= Q) ∧
    (¬ zq4 ((zVv Q).comp F7) →
      Hr Q = ⊤) := by
  let:=hp
  have hprime : (aum Q).IsPrime := by
    rw [bb3]
    exact zgL _
  constructor
  · intro hdom
    have hdisj:z1v (Ek :Set Lg) (aum Q:Set Lg) := by
      apply Set.disjoint_left.mpr
      rintro a ⟨b,hb,rfl⟩ hmem
      change znf b∈aum Q at hmem
      rw [bb3,zry] at hmem
      have hz :pD Q b=pD Q 0:= by
        simpa [wW] using hmem
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hb)
        ((c3w Q).2 hdom hz)
    have hcontract :=ztT Ek
      aiS hprime hdisj
    rw [bse] at hcontract
    refine ⟨bse Q ▸ znL Ek
      aiS _ hprime hdisj,?_⟩
    rw [← bfm,← zg6]
    change ((Hr Q).under Lg).comap CV= Q
    rw [hcontract,bb3]
    ext a
    change wW Q (CV a)=0↔a∈Q
    rw [← zQb,ax8,zQb,
      Polynomial.C_eq_zero,z1Q]
  · intro hdom
    have hn : ¬ zq4 (pD Q) :=
      fun h=>hdom ((c3w Q).1 h)
    obtain ⟨a,b,he,hab⟩:=Function.not_injective_iff.mp hn
    have hne :a - b∈aZ⁰:=mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hab)
    let d:Ek :=⟨znf (a - b),⟨a - b,hne,rfl⟩⟩
    have hd: (d:Lg)∈aum Q:= by
      rw [bb3,zry]
      simp [d,wW,he]
    have hmem:=z7X (z12 Lg aiS) hd
    rw [bse] at hmem
    exact (Hr Q).eq_top_of_isUnit_mem hmem (z0j aiS d)
end
end ac4
end
section
set_option backward.isDefEq.respectTransparency false
namespace ac4
noncomputable section
open cu gT pI ac3 Polynomial
open scoped Classical
private theorem bO9 {k l:Type} [zrb k] [zrb l]
  (f :k →+* l) (g:z3y (Fin 2) k) :
  (zDK f g).totalDegree≤g.totalDegree := by
 unfold MvPolynomial.totalDegree
 exact Finset.sup_mono (z88 f g)
theorem gtR {P:Jet} {s :Shape} (h:oU P s) :
   (aJA P).natDegree≤ s.J ∧
     ∀ j,((aJA P).coeff j).totalDegree≤ s.U:= by
 constructor
 · apply natDegree_le_iff_coeff_eq_zero.mpr
   intro j hj
   have hzero :P.coeff j=0:= by
     apply Polynomial.ext
     intro i
     simp only [zO6]
     by_contra hn
     exact (Nat.not_le_of_gt hj) (h j i hn).2.1
   simp [aJA,coeff_map,hzero]
 · intro j
   rw [aJA,coeff_map]
   change ((P.coeff j).eval₂ (zDK (z12 FX aQ))
     (znf (ek 1))).totalDegree≤ s.U
   rw [zI6,sum_def]
   apply MvPolynomial.totalDegree_finsetSum_le
   intro i hi
   rw [← zkq]
   refine (MvPolynomial.totalDegree_mul _ _).trans ?_
   rw [MvPolynomial.totalDegree_C,z0a]
   exact (bO9 _ _).trans (h j i (mem_support_iff.mp hi)).2.2
theorem de3 (I:znc z87) (P:Jet) :
    zVv (Hr I) (aMp (aJA P)) =
      zVv (Hr I) (Cl FX (iJ P)) := by
  let q:=zVv (Hr I)
  let f :=(q.comp (Cl FX)).comp oi
  let g:=q.comp (zHw (zQY (by decide :2≤4))).toRingHom
  have hy :f (z9v 2)=g (znf (ek 1)) := by
    change q (Cl FX
      ((zHw (zQY (by decide :3≤4))) (z9v 2))) =
      q ((MvPolynomial.rename (Fin.castLE (by decide :2≤4)))
        (znf (ek 1)))
    simp only [z6l,zt1,Cl,z7N]
    change q (z9v 2)=q (znf (ek 1))
    have hmem:Pp (2 :Fin 4)∈Hr I :=
      zs0 (zCn (zT1 _))
    have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hz' : q (z9v 2 - znf (ek 1))=0:=hz
    exact sub_eq_zero.mp (by simpa only [zpO] using hz')
  have hseeds :g.comp (zDK (z12 FX aQ))=f.comp pZ:= by
    apply zXT
    · intro a
      simp only [zQb,g,f,pZ,oi,Cl,
        ziQ,zlv,zt1,zpw]
    · intro i
      simp only [zQb,g,f,pZ,oi,Cl,
        ziQ,zlv,z6l,z7N]
      congr 2
  have hinner :g.comp (zqf
      (zDK (z12 FX aQ)) (znf (ek 1))) =
      f.comp A7:= by
    apply zz4
    intro A
    change g (A.eval₂ (zDK (z12 FX aQ)) (znf (ek 1))) =
      f (A.eval₂ pZ (z9v 2))
    rw [zly,zly,hseeds,hy]
  change q ((aJA P).eval₂
      (zHw (zQY (by decide :2≤4))).toRingHom (z9v 3)) =
    (q.comp (Cl FX)) (P.eval₂ (oi.comp A7) (z9v 3))
  rw [zly,zly,aJA,zem]
  have houter : (q.comp (Cl FX)).comp (oi.comp A7)=f.comp A7:=rfl
  rw [houter,← hinner]
  simp only [g,zQb,Cl,z7N]
private theorem gwL {k R ι:Type} [zrb k] [za6 R]
  [zZE k R] [Fintype ι] (D:znc R) (J:ι→ znc R)
  [zAa k (R ⧸ D)] (hle : ∀ i,D ≤J i)
  (hpair :zUQ fun i j=>zqs (J i) (J j)) :
  (∑ i,zsE k (R ⧸ J i))≤zsE k (R ⧸ D) := by
 let f (i:ι) :=z5F k (hle i)
 let (i:ι) :zAa k (R ⧸ J i) :=
  zIU (f i).toLinearMap (zuo (hle i))
 let F:=AlgHom.pi f
 have hF:zpX F:= by
  intro y
  obtain ⟨x,hx⟩:=Ideal.quotientInfToPiQuotient_surj hpair y
  obtain ⟨p,rfl⟩:=zld x
  exact ⟨zVv D p,funext fun i=>congrFun hx i⟩
 rw [← z0r]
 exact zs6 (f :=F.toLinearMap) hF
theorem bYt {I:znc z87} {P:Jet}
    (D:znc aiS)
    (hfinite :zAa aQ (aiS ⧸ D))
    (hcontains : ∀ Q∈aOS I P,D ≤Hr Q)
    (hloc : ∀ Q:znc z87,Q.IsPrime →
      Hr Q = ⊤ ∨
        ((Hr Q).IsPrime∧(Hr Q).comap (Cl FX)= Q)) :
    bDF (aOS I P)≤zsE aQ (aiS ⧸ D) := by
  classical
  let S:=aOS I P
  let J (i:S) :=Hr i.val
  have hle (i:S) :D ≤J i:=hcontains i.val i.property
  let:=hfinite
  have hq (i:S) :
      J i = ⊤ ∨ ((J i).IsMaximal∧(J i).comap (Cl FX)=i.val) := by
    have hp:=(Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp i.property).1).isPrime
    rcases hloc i.val hp with htop | ⟨hprime,hcomap⟩
    · exact zMH htop
    · let: (J i).IsPrime :=hprime
      let:zAa aQ (aiS ⧸ J i) :=
        zIU (z5F aQ (hle i)).toLinearMap
          (zuo (hle i))
      exact Or.inr ⟨zqX (J i)
        (IsField.of_isDomain_of_finite aQ (aiS ⧸ J i)),hcomap⟩
  have hpair :zUQ fun i j:S=>zqs (J i) (J j) := by
    intro i j hij
    rcases hq i with htop | ⟨hmaxi,hci⟩
    · simp [zDu,htop]
    rcases hq j with htop | ⟨hmaxj,hcj⟩
    · simp [zDu,htop]
    let:=hmaxi
    let:=hmaxj
    apply zoy
    intro heq
    apply hij
    apply zkt
    rw [← hci,← hcj,heq]
  have h:=gwL (k :=aQ) D J hle hpair
  rw [bDF,← zKD]
  exact h
theorem dSU {I Q:znc z87} {P:Jet}
  (hQ:Q∈aT1 I P) :
  Hr I ⊔ zye {aMp (aJA P)} ≤ Hr Q:= by
 have hmin:=Ideal.mem_minimalPrimesFinset.mp hQ
 have hle :I ⊔ zye {iJ P} ≤ Q:=hmin.le
 refine zbX (sup_le_sup (zi2 (le_sup_left.trans hle)) zs1) ?_
 apply (zvl _).mpr
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 rw [de3]
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 exact zKg (z7X _ (hle
  (zs0 (zCn (zT1 _)))))
end
end ac4
end
section
namespace ac4
noncomputable section
open cu gT pI ac3
def c1 :Prop :=
  ∀ (I:znc z87),I.IsPrime→ zqe (gk I)=2 →
    zq4 ((zVv I).comp F7) →
    zqe (as2 I)=1
def c2 :Prop :=
  ∀ (I:znc z87),
    zAa dV (ani I) →
    zAa aQ (Lj I) →
    zAa (CS aQ) (W1 (Hr I)) ∧
    zAa (CS aQ) (adm (Hr I)) ∧
    zsE (CS aQ) (W1 (Hr I)) =
      zsE dV (ani I) ∧
    zsE (CS aQ) (adm (Hr I)) =
      zsE aQ (Lj I)
def c3:Prop :=
  ∀ (k :Type) [zrb k] (H :znc (z3y (Fin 4) k)) (U J:ℕ)
    (G:zM1 (z3y (Fin 2) k)),
    H.IsPrime→ zqe (gk H)=1 →
    zAa (CS k) (W1 H) →
    zAa (CS k) (adm H) →
    G.natDegree≤J→(∀ j,(G.coeff j).totalDegree≤U)→aMp G∉H →
    zAa k (gk (H ⊔ zye {aMp G})) ∧
    zsE k (gk (H ⊔ zye {aMp G})) ≤
      U*zsE (CS k) (W1 H) +
      J*zsE (CS k) (adm H)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :
  ac3.c3:= by
 classical
 intro s I P _ hI hcaps hP
 obtain ⟨hprime,hcomap⟩:=(btg I hI.prime).1 hI.ordinate_dominant
 have hdim:=h1 I hI.prime hI.dimension hI.ordinate_dominant
 obtain ⟨hseed,hv,hseedrank,hvrank⟩:=h2 I hI.a6j hI.jet_finite
 obtain ⟨hdeg,hcoeff⟩:=gtR hcaps
 have hproper :aMp (aJA P)∉Hr I:= by
  intro h
  have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr h
  rw [de3] at hz
  have hmem:iJ P∈(Hr I).comap (Cl FX) :=
    show Cl FX (iJ P)∈Hr I from Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact hP (hcomap ▸ hmem)
 obtain ⟨hfinite,hlength⟩ :=
  h3 aQ (Hr I) s.U s.J (aJA P) hprime hdim
    hseed hv hdeg hcoeff hproper
 have hmass :=bYt (I:=I) (P:=P) _ hfinite
  (fun _ hQ=>dSU (Finset.mem_filter.mp hQ).1)
  (fun Q hp=> by
    by_cases hdom:zq4 ((zVv Q).comp F7)
    · exact Or.inr ((btg Q hp).1 hdom)
    · exact zMH ((btg Q hp).2 hdom))
 apply hmass.trans
 simpa [hseedrank,hvrank,dot,zRq,pN,zmL] using hlength
end
end ac4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace cy6
noncomputable section
open cu gT ac3 Polynomial
open scoped Polynomial
private theorem bx2 {A:Type} [za6 A] [ztn A] [zZE FX A]
   [zUK FX A] (hdim:zqe A=1) :
   zls FX A≤1 := by
 obtain ⟨d,f,hf,hfint⟩:=z4J FX A
 let B:=z3y (Fin d) FX
 let:zZE B A:=f.toRingHom.toAlgebra
 let:zsf FX B A:=zKB f
 let:zAa B A:=hfint
 let:zVK B A:=zux B A
 let:znE B A:=(zSO B A).mpr hf
 have hdB:zqe B=(d:zUi ℕ∞) := by
   simp [B,zmx,
     zZT]
 obtain ⟨l,hlen⟩:=Order.le_krullDim_iff.mp hdB.ge
 have :=l.head.isPrime
 have hle : (⊥ : znc A).under B≤l.head.asIdeal:= by
   change zK3 (z12 B A) ⊥ ≤ l.head.asIdeal
   rw [← zPx,
     (zli _).mp (zJj B A)]
   exact bot_le
 obtain ⟨P,_,hP,hPhead⟩:=zuu l.head.asIdeal
   (⊥ : znc A) hle
 let:P.IsPrime :=hP
 let:P.LiesOver l.head.asIdeal:=⟨hPhead.symm⟩
 obtain ⟨L,hL,_,_⟩:=z1m l P
 have hle : (d:zUi ℕ∞)≤ zqe A :=
   Order.le_krullDim_iff.mpr ⟨L,hL.trans hlen⟩
 rw [hdim] at hle
 have hd:d≤1 := by exact_mod_cast hle
 have ht:=z5k FX B (A:=A)
 rw [zBT (R:=B) (A:=A),z0a] at ht
 rw [← ht]
 change zls FX (z3y (Fin d) FX)≤1
 rw [zUx]
 simpa using (Nat.cast_le.mpr hd: (d:zpf.{0})≤(1 :ℕ))
private def parameters {A:Type} [za6 A] [zZE FX A] (a b:A) :
    aZ →ₐ[FX] A[X] :=
  ⟨zOD (C.comp (z12 FX A)) ![z7y,C a+Polynomial.X*C b],
    fun c=> by
      change zOD (C.comp (z12 FX A)) _ (znf c) =
        C (z12 FX A c)
      rw [zTv,zQb]⟩
@[simp] private theorem eJ7 {A:Type} [za6 A] [zZE FX A]
    (a b:A) (c:FX) :parameters a b (znf c)=C (z12 FX A c) :=
  (parameters a b).commutes c
@[simp] private theorem c3E {A:Type} [za6 A] [zZE FX A]
   (a b:A) :parameters a b (z9v 0)=Polynomial.X:= by
  simp [parameters]
@[simp] private theorem cbp {A:Type} [za6 A] [zZE FX A]
   (a b:A) :parameters a b (z9v 1)=C a+Polynomial.X*C b:= by
  simp [parameters]
private theorem eod {A:Type} [za6 A] [zZE FX A] {a b:A}
   (hm : ¬ (zxf FX a∧zxf FX b)) :
   Set.Infinite {c:FX | znN FX (a+algebraMap FX A c*b)} := by
 classical
 let:Infinite FX:=ztd _ (zxb L[X] FX)
 let z (c:FX) :=a+algebraMap FX A c*b
 change Set.Infinite {c:FX | ¬ zxf FX (z c)}
 by_cases h : ∃ c,zxf FX (z c)
 · obtain ⟨c,hc⟩:=h
   apply (Set.finite_singleton c).infinite_compl.mono
   intro d hd hda
   have hdc:d - c≠0:=sub_ne_zero.mpr (by simpa using hd)
   have he :z d - z c=z12 FX A (d - c)*b:= by
     dsimp [z]
     rw [zpO]
     ring
   have hmul :zxf FX (z12 FX A (d - c)*b) :=he ▸ hda.sub hc
   have hb:zxf FX b:= by
     have hh:=(zSH (A:=A) (d - c)⁻¹).mul hmul
     rwa [← ztg,← zok,inv_mul_cancel₀ hdc,zXs,zkF] at hh
   have ha :zxf FX a := by
     have hh:=hc.sub ((zSH (A:=A) c).mul hb)
     simpa [z] using hh
   exact hm ⟨ha,hb⟩
 · apply Set.infinite_univ.mono
   intro c _ hc
   exact h ⟨c,hc⟩
private theorem eKa {A:Type} [za6 A] [zZE FX A] {a b:A}
    (hm : ¬ (zxf FX a∧zxf FX b)) :
    zq4 (parameters a b) := by
  classical
  apply (zLn (parameters a b)).mpr
  intro p hp
  let e :=z8s FX 1
  let S:=z3y (Fin 1) FX
  let z (c:FX) :=a+algebraMap FX A c*b
  have hinf :=(eod hm).image
    (zbo (σ:=Fin 1) (R:=FX)).injOn
  have hz :e p=0:= by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinf.mono
    rintro _ ⟨c,hc,rfl⟩
    change zng (znf c) (e p)=zng (znf c) 0
    rw [zcG]
    let m:S →+* A:=zOD (z12 FX A) (fun _=>z c)
    have hm_eq :m=(zEU (z c)).toRingHom.comp
        (zpe FX (Fin 1)).toRingHom:= by
      apply zXT
      · intro r
        simp [m,zJG,zQb]
      · intro k
        simp [m,zJG,zQb]
    have hminj:zq4 m:= by
      rw [hm_eq]
      exact (transcendental_iff_injective.mp hc).comp
        (zpe FX (Fin 1)).injective
    have hcomp: (zhy (z12 FX A c)).comp (parameters a b).toRingHom =
        m.comp ((zhy (znf c)).comp e.toRingHom) := by
      apply zXT
      · intro r
        change zng (z12 FX A c) (parameters a b (znf r)) =
          m (zng (znf c) (e (znf r)))
        simp only [eJ7,e,zyf,zTv,
          zQb,zFf]
        have hr :zng (znf c:S) (C (znf r)) =
          MvPolynomial.C r := by apply zFf
        exact (zTv (z12 FX A) (fun _:Fin 1=>z c) r).symm.trans
          (zPw m hr.symm)
      · intro k
        change zng (z12 FX A c) (parameters a b (z9v k)) =
          m (zng (znf c) (e (z9v k)))
        have hk :k=0∨k=1 := by fin_cases k <;> decide
        rcases hk with rfl | rfl
        · rw [c3E,zB5,
            show e (z9v 0)=z7y from zOO,
            zB5]
          exact (zTv _ _ _).symm
        · rw [cbp,show e (z9v 1)=C (z9v 0) from
            z07 (j:=(0:Fin 1))]
          simp only [Polynomial.eval_add,Polynomial.eval_mul,zB5,zFf]
          have hx :zng (znf c:S) (C (z9v (0:Fin 1))) =
            z9v (0:Fin 1) := by apply zFf
          calc
            _=m (z9v (0:Fin 1)) :=
              (zrD (z12 FX A) (fun _:Fin 1=>z c) _).symm
            _ = _:=zPw m hx.symm
    apply (zLn m).mp hminj
    have h:=zLs hcomp p
    change zng (z12 FX A c) (parameters a b p) =
      m (zng (znf c) (e p)) at h
    exact h.symm.trans (by rw [hp,zcG])
  exact e.injective (hz.trans (zhc e).symm)
private theorem eJ8 {A:Type} [za6 A] [ztn A] [zZE FX A]
    [zUK FX A] (hdim:zqe A=1) (a b:A) :
    letI:zZE aZ A[X] :=(parameters a b).toRingHom.toAlgebra
    zjH aZ A[X] := by
  let f :=parameters a b
  let:zZE aZ A[X] :=f.toRingHom.toAlgebra
  change zjH aZ A[X]
  by_cases hf :zq4 f
  · let:znE aZ A[X] :=(zSO aZ A[X]).mpr hf
    let:zsf FX aZ A[X] :=zKB f
    have ht:=z5k FX aZ (A:=A[X])
    have hA:=z5k FX A (A:=A[X])
    have he :zls FX aZ=2 := by
      simp [zUx]
    rw [he] at ht
    rw [zBA] at hA
    have hsmall:zls FX A[X]≤2 := by
      rw [← hA]
      calc
        _≤(1 :zpf.{0})+1 :=zZP (bx2 hdim) zs1
        _=2 :=one_add_one_eq_two
    have hfin: (2 :zpf.{0})+Algebra.trdeg aZ A[X]≤2 :=
      ht.le.trans hsmall
    rw [← trdeg_eq_zero_iff]
    by_contra h
    have hpos : (1 :zpf)≤zls aZ A[X] :=Cardinal.one_le_iff_ne_zero.mpr h
    have hbad: (2 :zpf.{0})+1≤2 :=(zZP zs1 hpos).trans hfin
    have hn: (3:ℕ)≤2 := by exact_mod_cast hbad
    omega
  · exact Algebra.isAlgebraic_of_not_injective hf
private abbrev Over :=z3y (Fin 4) aQ
private abbrev extend:z87 →+* Over :=zDK (z12 FX aQ)
private abbrev i9 (Q:znc z87) (u v :z87) :znc Over :=
 Q.map extend ⊔ zye {extend u+MvPolynomial.C (ek 0)*extend v -
  znf (ek 1)}
private abbrev B6 (Q:znc z87) (u v :z87) :=Over ⧸ i9 Q u v
private def bd9 (Q:znc z87) (u v :z87) :gk Q →+* B6 Q u v :=
 z3G (i9 Q u v) extend (Ideal.map_le_iff_le_comap.mp le_sup_left)
private def aH0 (Q:znc z87) (u v :z87) :
  (gk Q)[X] →+* B6 Q u v :=
 zqf (bd9 Q u v) (z12 aQ (B6 Q u v) (ek 0))
private theorem gnN (Q:znc z87) (u v :z87) :
    bd9 Q u v (zVv Q u) +
      z12 aQ (B6 Q u v) (ek 0)*bd9 Q u v (zVv Q v) =
        z12 aQ (B6 Q u v) (ek 1) := by
  apply sub_eq_zero.mp
  have h:zVv (i9 Q u v)
      (extend u+MvPolynomial.C (ek 0)*extend v-MvPolynomial.C (ek 1))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show zye {_} ≤ i9 Q u v from le_sup_right)
        (z5J _))
  simpa only [zpO,zrl,zok,← zKm,
    zOY,bd9,z5h] using h
private theorem eJ9 (Q:znc z87) (u v :z87) :
    (aH0 Q u v).comp
      (parameters (zVv Q u) (zVv Q v)).toRingHom =
      (z12 aQ (B6 Q u v)).comp (z12 aZ aQ) := by
  apply zXT
  · intro c
    simp [aH0,bd9,zQb,zKm]
    rfl
  · intro i
    fin_cases i
    · simp [aH0,zQb,ek]
    · change aH0 Q u v
          (parameters (zVv Q u) (zVv Q v) (z9v 1)) =
        z12 aQ (B6 Q u v) (ek 1)
      simp only [cbp,zrl,zok,aH0,z4Q,
        zC9,zJU]
      exact gnN Q u v
private theorem cRR (Q:znc z87) [Q.IsPrime] (u v :z87)
    (hdim:zqe (gk Q)=1) :
    zAa aQ (B6 Q u v) := by
  let f :=parameters (zVv Q u) (zVv Q v)
  let:zZE aZ (gk Q)[X] :=f.toRingHom.toAlgebra
  have hAlg:zjH aZ (gk Q)[X] :=
    eJ8 (A:=gk Q) hdim (zVv Q u)
      (zVv Q v)
  let J:=i9 Q u v
  let q:=zVv J
  have hgen (i:Fin 4) :zsq aQ (q (z9v i)) := by
    let x :=C (zVv Q (z9v i))
    obtain ⟨p,hp,hz⟩:=hAlg.isAlgebraic x
    refine IsAlgebraic.isIntegral
      ⟨p.map (z12 aZ aQ),
        (zeI (zxb aZ aQ)).mpr hp,?_⟩
    have h:=zPw (aH0 Q u v) hz
    have hx :aH0 Q u v x=q (z9v i) := by
      change aH0 Q u v x=zVv (i9 Q u v) (z9v i)
      simp only [x,aH0,z4Q,zJU,bd9,
        z5h,z7N]
    have hcomm:=eJ9 Q u v
    change (aH0 Q u v).comp (z12 aZ (gk Q)[X])= _ at hcomm
    rwa [zhc,zCD,zly,hcomm,hx,
      ← zem,← zCD] at h
  refine (Algebra.finite_iff_isIntegral_and_finiteType (R:=aQ)
    (A:=B6 Q u v)).mpr ⟨⟨?_⟩,zWv⟩
  intro r
  obtain ⟨p,rfl⟩:=zld (I:=J) r
  change zsq aQ (q p)
  induction p using z5i with
  | C c =>
    simpa only [q,← zKm,zOY] using
      (z7i (A:=B6 Q u v) (x :=c))
  | add p p' hp hp' =>
    rw [zrl]
    exact IsIntegral.add (R:=aQ) (A:=B6 Q u v) hp hp'
  | mul_X p i hp =>
    rw [zok]
    exact IsIntegral.mul (R:=aQ) (A:=B6 Q u v) hp (hgen i)
private theorem eal (Q:znc z87) [Q.IsPrime] (u v :z87)
    (hinj:zq4 (parameters (zVv Q u) (zVv Q v))) :
    zue (B6 Q u v) := by
  let A:=gk Q
  let:za6 A:=z0w Q
  let:ztn A:=Ideal.Quotient.isDomain Q
  let F:=zNv A[X]
  let m:A[X] →+* F:=z12 _ _
  let f :=parameters (zVv Q u) (zVv Q v)
  let g:aQ →+* F:=zIj (g:=m.comp f.toRingHom)
    ((zxb A[X] F).comp hinj)
  have hg (d:aZ) :g (z12 aZ aQ d)=m (f d) :=
    zoc _ d
  let e :Over →+* F :=
    zOD g (fun i=>m (C (zVv Q (z9v i))))
  have he :e.comp extend=(m.comp C).comp (zVv Q) := by
    apply zXT
    · intro d
      have hd:z12 FX aQ d=z12 aZ aQ (znf d) :=rfl
      simp only [e,zQb,zpw,zTv,hd,hg]
      exact zPw m (f.commutes d)
    · intro i
      simp only [e,zQb,z7N,zrD]
      rfl
  have hker :i9 Q u v≤zdq e := by
    refine zbX (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro r hr
      change (e.comp extend) r=0
      rw [he]
      change m (C (zVv Q r))=0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr,zhc,zhc]
    · intro r hr
      obtain rfl :=Set.mem_singleton_iff.mp hr
      apply RingHom.mem_ker.mpr
      have hu:=zLs he u
      have hv :=zLs he v
      change e (extend u)=m (C (zVv Q u)) at hu
      change e (extend v)=m (C (zVv Q v)) at hv
      have hC (i:Fin 2) :e (znf (ek i))=m (f (z9v i)) :=
        (zTv g _ _).trans (hg _)
      rw [zpO,zrl,zok,hu,hv,hC 0,hC 1]
      change m (C (zVv Q u))+m (f (z9v 0)) *
        m (C (zVv Q v)) - m (f (z9v 1))=0
      simp only [f,c3E,cbp,zrl,zok]
      exact sub_self _
  let φ:B6 Q u v →+* F:=zP2 _ e hker
  exact nontrivial_of_ne (1 :B6 Q u v) 0 (fun h=>zOR (by
    simpa only [zXs,zhc] using zPw φ h))
theorem proof :ac3.c1 := by
 intro Q hQ hdim hMove
 let:Q.IsPrime :=hQ
 have hm : ¬ (zxf FX (zVv Q (z9v 0)) ∧
     zxf FX (zVv Q (z9v 1))) := by
   intro h
   apply hMove
   intro i
   fin_cases i
   · exact h.1
   · exact h.2
 let u:Ambient:=z9v 0
 let v :Ambient:=z9v 1
 have hseed :i9 Q u v= Q.map extend ⊔ zye {B4 0 1} := by
   simp [i9,u,v,B4]
 have hy :i9 Q (z9v 2) 0= Q.map extend ⊔ zye {Pp 2} := by
   simp [i9,Pp]
 have hSeed :zAa aQ (rM Q) := by
   change zAa aQ (Over ⧸ (Q.map extend ⊔ zye {B4 0 1}))
   rw [← hseed]
   exact cRR Q u v hdim
 let:zAa aQ (rM Q) :=hSeed
 let:zue (rM Q) := by
   change zue (Over ⧸ (Q.map extend ⊔ zye {B4 0 1}))
   rw [← hseed]
   exact eal Q u v (eKa hm)
 refine ⟨hSeed,zRt,?_⟩
 change zAa aQ (Over ⧸ (Q.map extend ⊔ zye {Pp 2}))
 rw [← hy]
 exact cRR Q (z9v 2) 0 hdim
end
end cy6
end
section
namespace axl
noncomputable section
open MM
open IsDedekindDomain
variable {F K:Type} [zrb F] [zrb K] [zZE F K]
def GV (B:Type) [za6 B] [zZE B K] (w:zZ F K) :Prop :=
 ∀ b:B,w.val (z12 B K b)≤1
def aMP {B:Type} [za6 B] [zJZ B]
    [zZE F B] [zZE B K] [zsf F B K] [z0o B K]
    (p:zZx B) :zZ F K where
  val :=p.valuation K
  surj:=p.valuation_surjective K
  trivial c hc:= by
    rw [zG3 F B K,p.valuation_eq_one_iff_notMem]
    exact fun hm=>p.isPrime.ne_top
      (zAn _ hm ((isUnit_iff_ne_zero.mpr hc).map (z12 F B)))
abbrev aFI (F:Type) [zrb F] :=
 (@zuT F _ (Classical.decEq _)).valuationSubring
instance gP6 (F:Type) [zrb F] :zZE F (aFI F) :=
 ((z12 F (ziC F)).codRestrict (aFI F).toSubring fun c=> by
   classical
   change zuT F (z12 F (ziC F) c)≤1
   rcases eq_or_ne c 0 with rfl | hc
   · simp
   · rw [z4W,RatFunc.inftyValuation.C F hc]).toAlgebra
instance eoh (F:Type) [zrb F] :zsf F (aFI F) (ziC F) :=
 zD8 rfl
end
end axl
end
section
set_option backward.isDefEq.respectTransparency false
namespace czk
noncomputable section
open gT WJ MM
open scoped TensorProduct
private theorem dVA {E F K B:Type}
   [zrb E] [zrb F] [zrb K] [za6 B] [zZE E B] [zZE F K]
   [zAa E B] (embed:E →+* F) (f :B →+* K)
   (hcomm : ∀ a,f (z12 E B a)=z12 F K (embed a))
   (hgen : ∀ S:zbh F K,(∀ b,f b∈S) → ∀ x :K,x∈S) :
   zAa F K∧zsE F K≤zsE E B:= by
 let:zZE E F:=embed.toAlgebra
 let:zZE E K:=((z12 F K).comp embed).toAlgebra
 let:zsf E F K:=zsL (fun _=>rfl)
 let fAlg:B →ₐ[E] K := { f with commutes' := hcomm }
 let q:F ⊗[E] B →ₐ[F] K:=AlgHom.liftEquiv E F B K fAlg
 let:zAa F q.range :=
   zIU q.rangeRestrict.toLinearMap q.rangeRestrict_surjective
 let S:zbh F K:=q.range.toIntermediateField fun x hx =>
   q.range.inv_mem_of_algebraic
     (Subalgebra.isAlgebraic_iff_isAlgebraic_val.mp (IsAlgebraic.of_finite F (⟨x,hx⟩:q.range)))
 have hmem (b:B) :f b∈S:= by
   change f b∈q.range
   exact q.mem_range.mpr ⟨1 ⊗ₜ[E] b,by simp [q,fAlg]⟩
 have hq:zpX q:= fun x=>q.mem_range.mp (hgen S hmem x)
 refine ⟨zIU q.toLinearMap hq,?_⟩
 calc
   zsE F K≤zsE F (F ⊗[E] B) :=
     zs6 hq
   _=zsE E B:=zXY
variable {k :Type} [zrb k] (D:znc (yT k)) [ztn (Cz D)]
private abbrev sU :=
 zvb (e7 k) ({Je D none} : Set (CurveField D))
set_option maxHeartbeats 600000 in
private theorem ds0 (S:zbh (sU D) (CurveField D))
   (hcoord : ∀ i,Je D i∈S) (x :CurveField D) :x∈S:= by
 let g:yT (e7 k) →+* CurveField D :=
   (z12 (Cz D) (CurveField D)).comp (zVv (Z9 D))
 have hX (i:zNO (Fin 2)) :g (z9v i)=Je D i:= by
   simp [g,Je,an9,Qe]
 have hC (a :e7 k) :g (znf a)∈S:= by
   change z12 (Cz D) (CurveField D) (z12 (e7 k) (Cz D) a)∈S
   rw [← zG3 (e7 k) (Cz D) (CurveField D)]
   have hm:=S.algebraMap_mem (z12 (e7 k) (sU D) a)
   exact ((sU D).val.commutes a) ▸ hm
 have hpoly (p:yT (e7 k)) :g p∈S:= by
   induction p using z5i with
   | C a=>exact hC a
   | add p q hp hq =>
     rw [g.map_add p q]
     exact S.add_mem hp hq
   | mul_X p i hp =>
     rw [g.map_mul p (z9v i),hX i]
     exact S.mul_mem hp (hcoord i)
 have ha (a :Cz D) :z12 (Cz D) (CurveField D) a∈S:= by
   obtain ⟨p,rfl⟩:=zld (I:=Z9 D) a
   exact hpoly p
 obtain ⟨a,b,_,rfl⟩:=zJC (Cz D) x
 exact S.div_mem (ha a) (ha b)
set_option maxHeartbeats 600000 in
theorem proof :MM.c3:= by
  intro k _ D _ hfinite
  let:=hfinite
  by_cases hv :zxf (e7 k) (Je D none)
  · exact zMH hv
  refine Or.inr ⟨hv,?_⟩
  let F:=e7 k
  let K:=CurveField D
  let L:=sU D
  let v :L:=⟨Je D none,IntermediateField.subset_adjoin F _ (zT1 _)⟩
  let pEval :zM1 k →+* L :=
    zqf ((z12 F L).comp (z12 k F)) v
  have hbase : (z12 L K).comp (z12 F L)=z12 F K :=
    zz4 (sU D).val.commutes
  have hp (p:zM1 k) :
      z12 L K (pEval p) =
        zEU (Je D none) (zGG (z12 k F) p) := by
    change z12 L K (p.eval₂ ((z12 F L).comp (z12 k F)) v)= _
    rw [zly,zCD,zem]
    rw [← zxS,hbase]
    rfl
  have hpInj:zq4 pEval := by
    intro p q h
    apply zTo (z12 k F) (z12 k F).injective
    exact (transcendental_iff_injective.mp hv)
      ((hp p).symm.trans ((zPw (z12 L K) h).trans (hp q)))
  let embed:JU k →+* L:=zIj hpInj
  let ev :z3y (Fin 2) (JU k) →+* K :=
    zOD ((z12 L K).comp embed) (fun i=>Je D (some i))
  have hev :ev.comp (awP k)=an9 D:= by
    apply zXT
    · intro a
      change ev (awP k (znf a)) =
        z12 (Cz D) K (zVv (Z9 D)
          (zDK (z12 k F) (znf a)))
      rw [zpw]
      rw [show awP k (znf a)=znf (z12 k (JU k) a) from
        zTv _ _ _]
      rw [show ev (znf (z12 k (JU k) a)) =
        z12 L K (embed (z12 k (JU k) a)) from zTv _ _ _]
      change z12 L K (embed (z12 k (JU k) a)) =
        z12 (Cz D) K (z12 F (Cz D) (z12 k F a))
      have heval :embed (z12 k (JU k) a)=pEval (z1z a) := by
        rw [zG3 k (zM1 k) (JU k) a]
        exact zoc hpInj _
      rw [heval,hp,zrL,z8q]
      exact zG3 F (Cz D) K (z12 k F a)
    · intro i
      change ev (awP k (z9v i))=Je D i
      rw [show awP k (z9v i)=i.elim
        (znf (z12 (zM1 k) (JU k) z7y)) z9v from
          zrD _ _ i]
      cases i with
      | none =>
        change ev (znf (z12 (zM1 k) (JU k) z7y)) =
          Je D none
        simp only [ev,zTv,zQb,embed,
          zoc,hp,zSo,zw0]
      | some i=>exact MvPolynomial.eval₂Hom_X' _ _ i
  let J:=D.map (awP k)
  let f :adm D →+* K:=zP2 J ev (by
    have hkill:J≤zdq ev := by
      rw [zo0,zEW,hev]
      intro p hp
      change z12 (Cz D) K (zVv (Z9 D) (Qe k p))=0
      have hz :zVv (Z9 D) (Qe k p)=0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (z7X (Qe k) hp)
      rw [hz,zhc]
    exact fun p hp=>hkill hp)
  have hfC (a :JU k) :f (z12 (JU k) (adm D) a)=z12 L K (embed a) := by
    change ev (znf a)= _
    exact zTv _ _ _
  refine dVA embed f hfC fun S hS=>ds0 D S ?_
  intro i
  cases i with
  | none=>exact S.algebraMap_mem v
  | some i =>
    have h:=hS (zVv J (z9v i))
    change ev (z9v i)∈S at h
    simpa only [ev,zrD] using h
end
end czk
end
section
set_option backward.isDefEq.respectTransparency false
namespace axl
noncomputable section
open MM
open IsDedekindDomain
open scoped WithZero nonZeroDivisors
private theorem gxN {K:Type} [zrb K] {v w:Valuation K ℤᵐ⁰}
   (h:v.IsEquiv w) (hv :zpX v) (hw:zpX w) :v=w:= by
 obtain ⟨x,hx⟩:=hv (zx0 1)
 have vxPow (n:ℤ) :v (x^n)=zx0 n:= by
   rw [map_zpow₀,hx,← zEp,zK0,zqg,ziL]
 have hxPos :1<w x := by
   have hpos :v 1<v x := by simp [hx]
   simpa only [zXs] using h.lt_iff_lt.mp hpos
 have hlogPos :0<zx3 (w x) :=
   (WithZero.lt_log_iff_exp_lt ((zero_lt_one.trans hxPos).ne')).mpr (by simpa using hxPos)
 obtain ⟨b,hb⟩:=hw (zx0 1)
 have hb' : v b≠0:=h.eq_zero.ne.mpr (by simp [hb])
 have hbPow:v (x^zx3 (v b))=v b:= by
   rw [vxPow,zFB hb']
 have hmul :zx3 (v b)*zx3 (w x)=1 := by
   have heq :=zPw zx3 (h.eq_iff.mp hbPow)
   simpa only [map_zpow₀,WithZero.log_zpow,zK0,ziL,id_eq,hb,zOL] using heq
 have hlog:zx3 (w x)=1 := by
   have hi:zWB (zx3 (w x)) :=IsUnit.of_mul_eq_one _ (by simpa [zDE] using hmul)
   rcases Int.isUnit_iff.mp hi with he | he <;> omega
 have hwx :w x=zx0 1 := by
   rw [← hlog,zFB ((zero_lt_one.trans hxPos).ne')]
 apply Valuation.ext
 intro a
 by_cases ha :a=0
 · simp [ha]
 have hxa :v (x^zx3 (v a))=v a := by
   rw [vxPow,zFB ((zyg v).mpr ha)]
 have hwa :=h.eq_iff.mp hxa
 rw [map_zpow₀,hwx,← zEp,zK0,zqg,
   ziL,zFB ((zyg v).mpr ha)] at hwa
 exact hwa
private theorem eLA {F K:Type} [zrb F] [zrb K] [zZE F K]
  {w w' : zZ F K} (h:w.val=w'.val) :w=w' := by
 cases w
 cases w'
 cases h
 rfl
theorem cE9 (F B K:Type) [zrb F] [za6 B] [zJZ B]
   [zrb K] [zZE F B] [zZE F K] [zZE B K] [zsf F B K] [z0o B K] :
   zq4 (aMP (F:=F) (K:=K) :zZx B→zZ F K) ∧
     ∀ w:zZ F K,GV B w → ∃ p:zZx B,aMP p=w:= by
 refine ⟨fun _ _ h=>zPZ K (zPw zZ.val h),?_⟩
 intro w hw
 let O:=w.val.valuationSubring
 let f :B →+* O:=(z12 B K).codRestrict O.toSubring fun b =>
   (zbt _ _).mpr (hw b)
 let P:=(zrY O).comap f
 have hP (b:B) :b∈P↔w.val (z12 B K b)<1 :=
   zNC K w.val (a :=f b)
 have hP0:P ≠ ⊥ := by
   intro hp
   have hval (b:B) (hb:b≠0) :w.val (z12 B K b)=1 := by
     refine zWs (hw b) (le_of_not_gt fun hlt=>hb ?_)
     have hmem:=(hP b).mpr hlt
     simpa only [hp,Ideal.mem_bot] using hmem
   obtain ⟨x,hx⟩:=w.surj (zx0 (-1))
   obtain ⟨n,d,hd,he⟩:=zJC B x
   have hn:n≠0:= by
     intro hz
     rw [hz,zhc,zero_div] at he
     rw [← he,zhc] at hx
     exact zBw hx.symm
   rw [← he,zsN,hval n hn,hval d (mem_nonZeroDivisors_iff_ne_zero.mp hd)] at hx
   simpa using hx.symm
 let p:zZx B :=
   ⟨P,zCL f (K:=zrY O),hP0⟩
 have hle : (p.valuation K).valuationSubring≤O:= by
   intro x hx
   obtain ⟨n,d,hnd⟩:=p.exists_primeCompl_mul_eq_of_integer x
     ((zbt _ _).mp hx)
   have hd1 :w.val (z12 B K d)=1 :=
     zWs (hw d) (le_of_not_gt fun hlt=>d.2 ((hP d).mpr hlt))
   have he :=zPw w.val hnd
   simp only [zok,hd1,zqg] at he
   apply (zbt w.val x).mpr
   rw [he]
   exact hw n
 have htop:O ≠ ⊤ := by
   intro h
   apply ((zt7 w.val).mp h)
   obtain ⟨x,hx⟩:=w.surj (zx0 1)
   exact ⟨x,by simp [hx],by simp [hx]⟩
 have heq : (p.valuation K).valuationSubring=O:= by
   rw [← p.valuationSubringAtPrime_eq_valuationSubring]
   exact z7D _ (by
     rwa [p.valuationSubringAtPrime_eq_valuationSubring]) htop
 have hequiv : (p.valuation K).IsEquiv w.val :=(Valuation.isEquiv_iff_valuationSubring ..).mpr heq
 exact ⟨p,eLA (gxN hequiv (p.valuation_surjective K) w.surj)⟩
end
end axl
end
section
set_option backward.isDefEq.respectTransparency false
namespace axl
noncomputable section
open MM
open IsDedekindDomain
open scoped Polynomial RatFunc WithZero nonZeroDivisors
def c1 :Prop :=
  ∀ (F B K:Type) [zrb F] [za6 B] [zJZ B] [zrb K]
    [zZE F B] [zZE F K] [zZE B K] [zsf F B K] [z0o B K]
    (a :B),a≠0→zAa F (B ⧸ zye {a}) →
    ∃ U:zJe (zZx B),
      (∀ p:zZx B,p∈U↔a∈p.asIdeal) ∧
      zsE F (B ⧸ zye {a}) =
        ∑ p∈U,QZ (aMP p:zZ F K) *
          KB (aMP p:zZ F K) (z12 B K a)
def c2 :Prop :=
  ∀ (F:Type) [zrb F] (a :aFI F),a≠0 →
    zAa F (aFI F ⧸ zye {a}) ∧
      (zsE F (aFI F ⧸ zye {a}) :ℤ) =
        -(z12 (aFI F) (ziC F) a).intDegree
private theorem degree_one {R:Type} [za6 R] [ztn R] (d:R→ℤ)
  (hd : ∀ x y :R,x≠0→y≠0→d (x*y)=d x+d y) :d 1=0:= by
 have h:=hd 1 1 zOR zOR
 rw [zkF] at h
 omega
private theorem degree_prod {R ι:Type} [za6 R] [ztn R] (d:R→ℤ)
   (hd : ∀ x y :R,x≠0→y≠0→d (x*y)=d x+d y)
   (s :zJe ι) (f :ι→R) (hf : ∀ i∈s,f i≠0) :
   d (∏ i∈s,f i) = ∑ i∈s,d (f i) := by
 classical
 induction s using zcw with
 | empty=>simp [degree_one d hd]
 | insert i s hi ih =>
   have hs : ∀ j∈s,f j≠0:= fun j hj=>hf j (zJN hj)
   rw [zqY hi,z5O hi,
     hd _ _ (hf i (zT5 i s)) (Finset.prod_ne_zero_iff.mpr hs),ih hs]
private theorem eQC {F R B:Type} [zrb F]
   [za6 R] [ztn R] [z8b R] [zZE F R]
   [za6 B] [ztn B] [zZE R B] [zZE F B] [zsf F R B]
   [zVy R B] [zAa R B] (d:R→ℤ)
   (hd : ∀ x y :R,x≠0→y≠0→d (x*y)=d x+d y)
   (hbase : ∀ a :R,a≠0→zAa F (R ⧸ zye {a}) ∧
     (zsE F (R ⧸ zye {a}) :ℤ)=d a)
   (a :B) (ha :a≠0) :
   zAa F (B ⧸ zye {a}) ∧
     (zsE F (B ⧸ zye {a}) :ℤ)=d (zXP R a) := by
 classical
 let b:=Module.Free.chooseBasis R B
 let I:znc B:=zye {a}
 have hI:I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
 let s :=I.smithCoeffs b hI
 have hs (i:zKb R B) :s i≠0:=I.smithCoeffs_ne_zero b hI i
 let (i:zKb R B) :zAa F (R ⧸ zye {s i}) :=
   (hbase _ (hs i)).1
 have hfin:zAa F (B ⧸ I) :=
   zZc ((I.quotientEquivPiSpan b hI).restrictScalars F).symm
 refine ⟨hfin,?_⟩
 have hsum:zsE F (B ⧸ I) = ∑ i,zsE F (R ⧸ zye {s i}) :=
   Ideal.finrank_quotient_eq_sum F b (hI:=hI)
 rw [hsum,Nat.cast_sum]
 simp_rw [(hbase _ (hs _)).2]
 rw [← degree_prod d hd Finset.univ s (fun i _=>hs i)]
 obtain ⟨u,hu⟩:=associated_norm_prod_smith b ha
 have hu0: (u:R)≠0:=Units.ne_zero u
 have huTop:zye ({(u:R)} : Set R) = ⊤ := Ideal.span_singleton_eq_top.mpr u.isUnit
 have huRank :zsE F (R ⧸ zye ({(u:R)} : Set R))=0:= by
   rw [huTop]
   exact zuF
 have huDeg:d (u:R)=0:= by simpa [huRank] using (hbase (u:R) hu0).2.symm
 rw [← hu,hd _ _ (Algebra.norm_ne_zero_iff.mpr ha) hu0,huDeg,z0a]
section Chart
variable {F K:Type} [zrb F] [zrb K] [zZE F K]
private def awt (w:zZ F K) (g:K) :ℤ :=
 (QZ w:ℤ)*zx3 (w.val g)
private theorem gqZ (w:zZ F K) {x y :K} (hx :x≠0) (hy :y≠0) :
  awt w (x/y)=awt w x-awt w y := by
 simp only [awt,zsN,WithZero.log_div ((zyg w.val).mpr hx)
  ((zyg w.val).mpr hy),mul_sub]
private theorem cJX (U:zJe (zZ F K)) (g:K) :
  ∑ w∈U,awt w g=(af8 U g:ℤ)-(aAJ U g:ℤ) := by
 simp only [af8,aAJ,Nat.cast_sum,← zQr,
  Nat.cast_mul,awt,← mul_sub]
 refine zUo rfl fun w _=>zPw ((QZ w:ℤ) * ·) ?_
 unfold poleOrder KB
 omega
private theorem eoD (h1 :c1) {B:Type} [za6 B]
    [zJZ B] [zZE F B] [zZE B K] [zsf F B K] [z0o B K]
    (a :B) (ha :a≠0) (hfin:zAa F (B ⧸ zye {a})) :
    ∃ U:zJe (zZ F K),
      (∀ w∈U,GV B w) ∧
      (∀ w,GV B w→w.val (z12 B K a)≠1→w∈U) ∧
      (∑ w∈U,awt w (z12 B K a)) =
        -(zsE F (B ⧸ zye {a}) :ℤ) := by
  obtain ⟨I,hI,hsum⟩:=h1 F B K a ha hfin
  let e :zZx B ↪ zZ F K:=⟨aMP,(cE9 F B K).1⟩
  refine ⟨I.map e,?_,?_,?_⟩
  · intro w hw
    obtain ⟨p,_,rfl⟩:=Finset.mem_map.mp hw
    intro b
    exact p.valuation_le_one (K:=K) b
  · intro w hw hne
    obtain ⟨p,rfl⟩:=(cE9 F B K).2 w hw
    refine Finset.mem_map.mpr ⟨p,(hI p).mpr ?_,rfl⟩
    by_contra hn
    exact hne ((p.valuation_eq_one_iff_notMem (K:=K)).mpr hn)
  · have hpole :af8 (I.map e) (z12 B K a)=0:= by
      refine zYF fun w hw => ?_
      obtain ⟨p,_,rfl⟩:=Finset.mem_map.mp hw
      have hle :=p.valuation_le_one (K:=K) a
      have hne :=(zyg (p.valuation K)).mpr
        ((zw1 _ (zxb B K)).mpr ha)
      have hle' : zx3 (p.valuation K (z12 B K a))≤0 :=
        (z8p hne).mpr (by simpa using hle)
      have hn:poleOrder (e p) (z12 B K a)=0:=Int.toNat_of_nonpos hle'
      simp [hn]
    rw [cJX,hpole,zQq,zero_sub]
    congr 1
    unfold aAJ
    rw [z93]
    exact_mod_cast hsum.symm
private theorem cVm {R:Type} [za6 R] [zZE R K]
   (w:zZ F K) :
   GV (zwB R K) w ↔ ∀ r :R,w.val (z12 R K r)≤1 := by
 constructor
 · intro h r
   simpa only [← zG3 R (zwB R K) K] using
     h (z12 R (zwB R K) r)
 · intro h a
   let O:=w.val.valuationSubring
   let:zZE R O:=((z12 R K).codRestrict O.toSubring fun r=> by
     exact (zbt _ _).mpr (h r)).toAlgebra
   let:zsf R O K:=zD8 rfl
   exact (z9W w.val).isIntegral_iff_v_le_one.mp
     ((a.2 :zsq R (a :K)).tower_top (A:=O))
private theorem adr (h1 :c1) {R L:Type}
    [za6 R] [ztn R] [z8b R] [zZE F R]
    [zrb L] [zZE R L] [z0o R L] [zZE L K] [zZE R K]
    [zsf R L K] [zsf F R K] [zAa L K] [zw7 L K]
    (d:L→ℤ) (hd : ∀ x y :L,x≠0→y≠0→d (x*y)=d x+d y)
    (hbase : ∀ a :R,a≠0→zAa F (R ⧸ zye {a}) ∧
      (zsE F (R ⧸ zye {a}) :ℤ)=d (z12 R L a))
    (g:K) (hg:g≠0) :
    ∃ U:zJe (zZ F K),
      (∀ w∈U,∀ r :R,w.val (z12 R K r)≤1) ∧
      (∀ w,(∀ r :R,w.val (z12 R K r)≤1)→w.val g≠1→w∈U) ∧
      (∑ w∈U,awt w g) = -d (zXP L g) := by
  classical
  let B:=zwB R K
  let:zZE F B:=((z12 R B).comp (z12 F R)).toAlgebra
  let:zsf F R B:=zD8 rfl
  let:zsf F B K:=zsL fun x=> by
    change z12 F K x=z12 B K (z12 R B (z12 F R x))
    rw [← zG3,← zG3]
  let:zJZ B:=zGd R L K B
  let:zAa R B:=za2 R L K B
  let:Module.IsTorsionFree R K := .trans_faithfulSMul R L K
  let:zVy R B:=IsIntegralClosure.module_free R L K B
  let:z0o B K:=IsIntegralClosure.isFractionRing_of_finite_extension R L K B
  let:zNo (zTz B R⁰) K :=
    IsIntegralClosure.isLocalization R L K B
  have hArg {a :B} (ha :a≠0) :
      ∃ U:zJe (zZ F K),(∀ w∈U,GV B w) ∧
        (∀ w,GV B w→w.val (z12 B K a)≠1→w∈U) ∧
        (∑ w∈U,awt w (z12 B K a)) =
          -d (zXP L (z12 B K a)) := by
    have ⟨hf,hn⟩:=eQC (fun r :R=>d (z12 R L r))
      (fun x y hx hy=> by
        rw [zok]
        exact hd _ _ ((zw1 _ (zxb R L)).mpr hx)
          ((zw1 _ (zxb R L)).mpr hy)) hbase a ha
    obtain ⟨U,hU,hsupport,hweight⟩:=eoD (F:=F) (K:=K) h1 a ha hf
    exact ⟨U,hU,hsupport,by
      rw [hweight,hn,Algebra.norm_localization R R⁰ (Rₘ:=L) (Sₘ:=K)]⟩
  obtain ⟨a,b,hb,hab⟩:=zJC B g
  have ha :a≠0:= by
    intro hz
    apply hg
    rw [← hab,hz,zhc,zero_div]
  have hb' : b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
  obtain ⟨U,hU,hsU,hwU⟩:=hArg ha
  obtain ⟨V,hV,hsV,hwV⟩:=hArg hb'
  have bsx (w:zZ F K) (hw:w∈U∪V) :GV B w :=
    (Finset.mem_union.mp hw).elim (hU w) (hV w)
  have hx :z12 B K a≠0 :=
    (zw1 _ (zxb B K)).mpr ha
  have hy :z12 B K b≠0:=IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨U∪V,fun w hw=>(cVm w).mp (bsx w hw),?_,?_⟩
  · intro w hw hne
    have hw' : GV B w:=(cVm w).mpr hw
    by_contra hout
    rw [← hab,zsN,
      not_not.mp (mt (hsU w hw') (fun h=>hout (zDk _ h))),
      not_not.mp (mt (hsV w hw') (fun h=>hout (zMj _ h))),div_one] at hne
    exact hne rfl
  · have enlarge {W:zJe (zZ F K)} (hW:W⊆U∪V) (z :K)
        (hs : ∀ w,GV B w→w.val z≠1→w∈W) :
        (∑ w∈W,awt w z) = ∑ w∈U∪V,awt w z :=
      zVG hW fun w hw hn=> by
        have hval :w.val z=1 :=not_not.mp (mt (hs w (bsx w hw)) hn)
        simp [awt,hval]
    have hdDiv (x y :L) (hx' : x≠0) (hy' : y≠0) :d (x/y)=d x - d y := by
      have h:=hd (x/y) y (div_ne_zero hx' hy') hy'
      rw [div_mul_cancel₀ _ hy'] at h
      omega
    have hnorm:zXP L (z12 B K a/z12 B K b) =
        zXP L (z12 B K a)/zXP L (z12 B K b) := by
      simp only [div_eq_mul_inv,zok,Algebra.norm_inv]
    rw [← hab,hnorm,hdDiv _ _ (Algebra.norm_ne_zero_iff.mpr hx)
      (Algebra.norm_ne_zero_iff.mpr hy)]
    simp_rw [gqZ _ hx hy,zQr]
    rw [← enlarge Finset.subset_union_left _ hsU,← enlarge Finset.subset_union_right _ hsV,
      hwU,hwV]
    omega
end Chart
private theorem eM1 {F:Type} [zrb F] (a :F[X]) (ha :a≠0) :
  zAa F (F[X] ⧸ zye {a}) ∧
  (zsE F (F[X] ⧸ zye {a}) :ℤ)=(z12 F[X] (ziC F) a).intDegree := by
 exact ⟨(zY5 ha).finite,by
  rw [ztb]
  exact_mod_cast (zY5 ha).finrank⟩
theorem cU9 (F:Type) [zrb F] :z8E (aFI F) := by
 classical
 let:IsCyclic (ℤᵐ⁰)ˣ :=
   isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm
     WithZero.unitsWithZeroEquiv.symm.surjective
 change z8E (zuT F).valuationSubring
 infer_instance
section RationalLine
variable {F K:Type} [zrb F] [zrb K] [zZE F K]
local notation "OI" => RatFunc F
local notation "aRl" => Polynomial F
local notation "Dc" => aFI F
set_option maxHeartbeats 1500000 in
private theorem fTH (h1 :c1) (h2 :c2)
    [zZE OI K] [zsf F OI K] [zAa OI K] [zw7 OI K]
    (g:K) (hg:g≠0) (S:zJe (zZ F K)) :
    ∃ T:zJe (zZ F K),aAJ S g≤af8 T g:= by
  classical
  let aS4 :zZE Dc OI:=zWv
  let:zZE Dc OI:=aS4
  let:SMul Dc OI:=aS4.toSMul
  let:zsf F Dc OI:=eoh F
  let:z8E Dc:=cU9 F
  let:zZE aRl K:=((z12 OI K).comp (z12 aRl OI)).toAlgebra
  let:zsf aRl OI K:=zD8 rfl
  let:zsf F aRl K:=zsL fun x=> by
    change z12 F K x=z12 OI K (z12 aRl OI (z12 F aRl x))
    rw [← zG3 F aRl OI,← zG3 F OI K]
  let:zZE Dc K:=((z12 OI K).comp (z12 Dc OI)).toAlgebra
  let:zsf Dc OI K:=zD8 (R:=Dc) (S:=OI) (A:=K) rfl
  let:zsf F Dc K:=zsL fun x=> by
    change z12 F K x=z12 OI K (z12 Dc OI (z12 F Dc x))
    rw [← zG3 F Dc OI,← zG3 F OI K]
  obtain ⟨U,hU,hsU,hwU⟩ :=
    adr h1 (R:=aRl) (L:=OI) zfy
      (fun _ _ hx hy=>zro hx hy) eM1 g hg
  obtain ⟨V,hV,hsV,hwV⟩ :=
    adr h1 (R:=Dc) (L:=OI) (fun x => -x.intDegree)
      (fun _ _ hx hy=> by rw [zro hx hy,neg_add]) (h2 F) g hg
  let restrict (w:zZ F K) :Valuation OI ℤᵐ⁰:=w.val.comap (z12 OI K)
  let (w:zZ F K) : (restrict w).IsTrivialOn F:=⟨fun c hc=> by
    change w.val (z12 OI K (z12 F OI c))=1
    rw [← zG3 F OI K]
    exact w.trivial c hc⟩
  have hnontrivial (w:zZ F K) : (restrict w).IsNontrivial:= by
    by_contra h
    let:w.val.IsTrivialOn OI:=⟨fun a ha=> by
      change restrict w a=1
      by_contra hv
      exact h ⟨a,(zyg (restrict w)).mpr ha,hv⟩⟩
    obtain ⟨b,hb⟩:=w.surj (zx0 1)
    have hb0:b≠0:= by
      intro h0
      rw [h0,zhc] at hb
      exact zBw hb.symm
    have hb1 :w.val b≠1 := by
      rw [hb,← zva,ne_eq,WithZero.exp_inj]
      decide
    exact (w.val.transcendental_of_ne_one OI b hb0 hb1)
      (zgs b)
  have hdisj:z1v U V:= by
    refine Finset.disjoint_left.mpr fun w hu hv => ?_
    have hleO: (zuT F).valuationSubring≤(restrict w).valuationSubring := by
      intro a ha
      exact (zbt (restrict w) a).mpr (hV w hv ⟨a,ha⟩)
    have hEq:=z7D _ hleO
      (fun h=>((zt7 (restrict w)).mp h) (hnontrivial w))
    have hle :=hU w hu z7y
    change restrict w (zyX:OI)≤1 at hle
    have hm:zyX∈(restrict w).valuationSubring :=
      (zbt _ _).mpr hle
    rw [← hEq] at hm
    have hh:=(zbt _ _).mp hm
    rw [RatFunc.inftyValuation.X,← zva,zSP] at hh
    omega
  have hcover (w:zZ F K) (hw:w.val g≠1) :w∈U∪V:= by
    rcases le_or_gt (restrict w zyX) 1 with hle | hlt
    · refine zDk _ (hsU w ?_ hw)
      intro a
      exact Polynomial.valuation_le_one_of_valuation_X_le_one F hle a
    · refine zMj _ (hsV w ?_ hw)
      intro a
      have h:=RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
      exact h.le_one_iff_le_one.mpr a.2
  have hsum: (∑ w∈U∪V,awt w g)=0:= by
    rw [Finset.sum_union hdisj,hwU,hwV]
    omega
  rw [cJX] at hsum
  have hpart:aAJ S g≤aAJ (U∪V) g:= by
    unfold aAJ
    calc
      _ = ∑ w∈S∩(U∪V),QZ w*KB w g:= by
        symm
        apply zVG Finset.inter_subset_left
        intro w hw hn
        have hval :w.val g=1 := by
          by_contra hv
          exact hn (Finset.mem_inter.mpr ⟨hw,hcover w hv⟩)
        simp [KB,hval]
      _≤_:=Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _=>zD0 _)
  exact ⟨U∪V,hpart.trans (by omega)⟩
end RationalLine
theorem of_children (h1 :c1) (h2 :c2) :MM.c7:= by
 intro F K _ _ _ hsep g hg S
 obtain ⟨t,ht,htFin,htSep⟩:=hsep
 let E :=zvb F {t}
 let L:=ziC F
 let e :L ≃ₐ[F] E :=RatFunc.algEquivOfTranscendental t ht
 let f :L →ₐ[F] K:=E.val.comp e.toAlgHom
 let:zZE L K:=f.toRingHom.toAlgebra
 let:zsf F L K:=zKB f
 have hmaps : (z12 L K).comp e.symm.toRingHom=(zqD K).toRingHom.comp
     (z12 E K) := by
   ext x
   change (e (e.symm x) :K)=(x :K)
   rw [e.apply_symm_apply]
 let:zAa E K:=htFin
 let:zw7 E K:=htSep
 let:zAa L K:=Module.Finite.of_equiv_equiv e.symm.toRingEquiv (zqD K) hmaps
 let:zw7 L K :=
   Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (zqD K) hmaps
 exact fTH h1 h2 g hg S
end
end axl
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace bzV
noncomputable section
open cu gT WJ
open scoped Polynomial
private abbrev abZ (I:znc z87) :=(gk I)[X]
local instance (I:znc z87) :za6 (abZ I) :=
 @Polynomial.commRing (gk I) (z0w I)
private def qw (I:znc z87) :aZ →+* abZ I :=
 zOD (Polynomial.C.comp (z12 FX (gk I)))
  ![z7y,z1z (UW I 2) +
    z7y*z1z (UW I 3)]
private theorem cbo (I:znc z87) :
  qw I (z9v 0)=Polynomial.X :=
 zrD _ _ _
private theorem c3B (I:znc z87) :
  qw I (z9v 1)=z1z (UW I 2) +
   z7y*z1z (UW I 3) :=
 zrD _ _ _
private theorem bKi (I:znc z87)
  (hvar : ¬ zxf FX (UW I 2) ∨ ¬ zxf FX (UW I 3)) :
  zq4 (qw I) := by
 let:Infinite FX:=ztd _ (zxb L[X] FX)
 exact eJ4 (k :=FX) (A:=gk I)
  (UW I 2) (UW I 3) hvar
private def toSlice (I:znc z87) :gk I →+* XS I :=
 z3G (RV I) Mv (zzQ)
private def vV (I:znc z87) :abZ I →+* XS I :=
 zqf (toSlice I) (z12 aQ (XS I) (ek 0))
private theorem bNY (I:znc z87) :
   toSlice I (UW I 2)+algebraMap aQ (XS I) (ek 0) *
     toSlice I (UW I 3)=z12 aQ (XS I) (ek 1) := by
 let m:=zVv (RV I)
 change m (Mv (z9v 2))+m (znf (ek 0)) *
   m (Mv (z9v 3))=m (znf (ek 1))
 rw [← zok,← zrl]
 congr 1
 simp [Mv]
private theorem aEa (I:znc z87) :
    (vV I).comp (qw I) =
      (z12 aQ (XS I)).comp (z12 aZ aQ) := by
  apply zXT
  · intro a
    simp [qw,vV,zQb,toSlice,Mv]
    rfl
  · intro k
    fin_cases k
    · change vV I (qw I (z9v 0)) =
        z12 aQ (XS I) (ek 0)
      rw [cbo,vV,z4Q,zC9]
    · change vV I (qw I (z9v 1)) =
        z12 aQ (XS I) (ek 1)
      rw [c3B]
      simp only [zrl,zok,vV,z4Q,
        zJU,zC9]
      exact bNY I
private abbrev e7 (I:znc z87) :=zNv (abZ I)
private def aM0 (I:znc z87) [I.IsPrime]
  (hinj:zq4 (qw I)) :aQ →+* e7 I :=
 zIj (K:=aQ)
  (g:=(z12 (abZ I) (e7 I)).comp (qw I))
  ((zxb (abZ I) (e7 I)).comp hinj)
private theorem bcE (I:znc z87) [I.IsPrime]
  (hinj:zq4 (qw I)) (r :aZ) :
  aM0 I hinj (z12 aZ aQ r) =
    z12 (abZ I) (e7 I) (qw I r) :=
 zoc _ r
private def buY (i:zNO (Fin 2)) :Fin 4 :=
 i.elim 3 (zVs 2)
private def a6J (I:znc z87) [I.IsPrime] (hinj:zq4 (qw I)) :
  yT aQ →+* e7 I :=
 zOD (aM0 I hinj) (fun i =>
  z12 (abZ I) (e7 I) (z1z (UW I (buY i))))
private theorem eyY {A B:Type} [za6 A] [za6 B]
  (f :A →+* B) (y v t:A) :f (y+t*v) - f t*f v=f y := by
 rw [← f.map_mul,← f.map_sub,zY6]
private theorem bti (I:znc z87) [I.IsPrime]
    (hinj:zq4 (qw I)) :
    (a6J I hinj).comp Mv =
      ((z12 (abZ I) (e7 I)).comp z1z).comp (zVv I) := by
  apply zXT
  · intro a
    simp only [zQb,Mv,a6J,zTv]
    change aM0 I hinj (z12 aZ aQ (znf a))= _
    rw [← zKm FX (Fin 4),zOY]
    simpa only [qw,zTv,zQb] using
      bcE I hinj (znf a)
  · intro i
    let f :=a6J I hinj
    let m:=z12 (abZ I) (e7 I)
    have hX (j:zNO (Fin 2)) :
        f (z9v j)=m (z1z (UW I (buY j))) :=
      zrD _ _ _
    have hC (j:Fin 2) :f (znf (ek j))=m (qw I (z9v j)) :=
      (zTv _ _ _).trans (bcE I hinj _)
    change f (Mv (z9v i))=m (z1z (UW I i))
    rw [Mv,zrD]
    fin_cases i
    · exact hX (some 0)
    · exact hX (some 1)
    · change f (znf (ek 1) -
          znf (ek 0)*z9v none)= _
      rw [f.map_sub,f.map_mul,hC 0,hC 1,hX none,cbo,c3B]
      exact eyY (A:=abZ I) (B:=e7 I) m
        (z1z (UW I 2)) (z1z (UW I 3)) z7y
    · exact hX none
private def aE0 (I:znc z87) [I.IsPrime] (hinj:zq4 (qw I)) :
  XS I →+* e7 I :=
 zP2 (RV I) (a6J I hinj) <| by
  change I.map Mv≤zdq (a6J I hinj)
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change ((a6J I hinj).comp Mv) a=0
  rw [bti]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
private theorem cpQ (I:znc z87) [I.IsPrime]
    (hinj:zq4 (qw I)) :
    (aE0 I hinj).comp (vV I)=z12 (abZ I) (e7 I) := by
  apply z86
  · intro a
    obtain ⟨a,rfl⟩:=zld a
    simpa [aE0,vV,toSlice,zQb] using
      zLs (bti I hinj) a
  · simp only [zQb,vV,z4Q,zC9]
    change aE0 I hinj (zVv (RV I)
        (znf (ek 0)))= _
    rw [aE0,z0R,a6J,zTv,ek,
      bcE,cbo]
private theorem aQr (I:znc z87) [I.IsPrime]
  (hinj:zq4 (qw I)) :zq4 (vV I) := by
 have hf :zq4 ((aE0 I hinj).comp (vV I)) := by
  rw [cpQ]
  exact zxb _ _
 exact Function.Injective.of_comp hf
private theorem aG3 (I:znc z87) (x :XS I) :
    ∃ (q:abZ I) (r :aZ),r≠0 ∧
      x*z12 aQ (XS I) (z12 aZ aQ r)=vV I q:= by
  let:zZE (z3y (zNO (Fin 2)) aZ) (yT aQ) :=
    MvPolynomial.algebraMvPolynomial
  obtain ⟨f,rfl⟩:=zld x
  obtain ⟨⟨g,m⟩,hgm⟩:=IsLocalization.surj
    (M:=(zgt aZ).map (znf (σ:=zNO (Fin 2)))) f
  obtain ⟨r,hr,hrm⟩:=m.property
  let lift:z3y (zNO (Fin 2)) aZ →+* abZ I:=zOD (qw I)
    (fun i=>z1z (UW I (buY i)))
  have hcomp: (vV I).comp lift=(zVv (RV I)).comp
      (zDK (z12 aZ aQ)) := by
    apply zXT
    · intro a
      simp only [zQb,lift,zTv,zpw]
      rw [← zKm,zOY]
      exact zLs (aEa I) a
    · intro i
      cases i with
      | none=>simp [lift,vV,toSlice,UW,Mv,RingHom.comp_apply,buY]
      | some i =>
        fin_cases i <;>
          simp [lift,vV,toSlice,UW,Mv,zQb,buY]
  refine ⟨lift g,r,mem_nonZeroDivisors_iff_ne_zero.mp hr,?_⟩
  have hgm' : f*znf (z12 aZ aQ r) =
      zDK (z12 aZ aQ) g:= by
    simpa only [zu8,← hrm,zpw] using hgm
  calc
    _=zVv (RV I) (f*znf (z12 aZ aQ r)) :=
      (zok _ _ _).symm
    _ = _:=(zPw (zVv (RV I)) hgm').trans
      (zLs hcomp g).symm
private theorem gr6 (I:znc z87) [I.IsPrime]
  (hinj:zq4 (qw I)) : (RV I).comap Mv=I:= by
 refine zWs ?_ zzQ
 intro a ha
 have hz :toSlice I (zVv I a)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr ha
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 apply zmy
 apply aQr I hinj
 simpa only [vV,z4Q,zJU,zhc] using hz
private theorem deu (I:znc z87) [I.IsPrime]
   (hinj:zq4 (qw I)) :
   let:zZE (abZ I) (XS I) :=(vV I).toAlgebra
   zNo ((zgt aZ).map (qw I)) (XS I) := by
 let:zZE (abZ I) (XS I) :=(vV I).toAlgebra
 refine ⟨⟨?_,?_,?_⟩⟩
 · rintro ⟨_,r,hr,rfl⟩
   change zWB ((vV I).comp (qw I) r)
   rw [aEa]
   apply IsUnit.map (z12 aQ (XS I))
   apply isUnit_iff_ne_zero.mpr
   simpa only [zhc] using
     (zxb aZ aQ).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)
 · intro x
   obtain ⟨q,r,hr,hx⟩:=aG3 I x
   refine ⟨⟨q,⟨qw I r,⟨r,mem_nonZeroDivisors_iff_ne_zero.mpr hr,rfl⟩⟩⟩,?_⟩
   change x*((vV I).comp (qw I)) r=vV I q
   rwa [aEa]
 · intro x y h
   exact ⟨1,by rw [aQr I hinj h]⟩
private def gsy (I:znc z87) :abZ I →ₐ[FX] XS I :=
 ⟨vV I,fun a=> by
   change vV I (z1z (z12 FX (gk I) a))= _
   have h:=zLs (aEa I) (znf a)
   simp only [zQb,qw,zTv] at h
   exact h⟩
private theorem gr8 (I:znc z87) [I.IsPrime] [ztn (XS I)]
  (d:ℕ) (hdim:zqe (gk I)=((d+1 :ℕ) :zUi ℕ∞))
  (hinj:zq4 (qw I)) :
  zqe (XS I)=(d:zUi ℕ∞) := by
 let:zZE (abZ I) (XS I) :=(vV I).toAlgebra
 have :=deu I hinj
 have hAlg:zjH (abZ I) (XS I) :=
  zyQ _ ((zgt aZ).map (qw I))
 exact dsH (k :=FX) (E :=aQ) (A:=gk I)
  (B:=XS I) (gsy I) (aQr I hinj) hAlg (eJ2 FX) d hdim
theorem proof :WJ.c1 := by
 intro I d hprime hdim hvar
 let:I.IsPrime :=hprime
 have hinj:=bKi I hvar
 let:zZE (abZ I) (XS I) :=(vV I).toAlgebra
 have :=deu I hinj
 have hM: (zgt aZ).map (qw I)≤zgt (abZ I) := by
   rintro _ ⟨r,hr,rfl⟩
   exact mem_nonZeroDivisors_iff_ne_zero.mpr
     (fun h=>(mem_nonZeroDivisors_iff_ne_zero.mp hr) (hinj (h.trans (zhc _).symm)))
 have :ztn (XS I) :=IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
 exact ⟨(Ideal.Quotient.isDomain_iff_prime _).mp zWv,
   gr8 I d hdim hinj,gr6 I hinj⟩
end
end bzV
end
section
set_option maxHeartbeats 800000
namespace czh
noncomputable section
open cu gT pI WJ MvPolynomial
open scoped nonZeroDivisors
private abbrev a96 (k :Type) [zrb k] :=z3y (Fin 4) k
private abbrev bzo (k :Type) [zrb k] :=z3y (Fin 2) k
private abbrev aBg (k :Type) [zrb k] :=z3y (Fin 2) (bzo k)
private abbrev aua (k :Type) [zrb k] :=z3y (Fin 2) (Ez k)
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance gQc (k :Type) [zrb k] :
    z0o (aBg k) (Ez (Ez k)) := by
  let M:zdT (aBg k) :=(zgt (bzo k)).map C
  have :zNo M (aua k) :=
    zEY (zgt (bzo k)) (Ez k)
  have hcomap : (zgt (aua k)).comap
      (z12 (aBg k) (aua k))=zgt (aBg k) := by
    have hinj:zq4 (z12 (aBg k) (aua k)) :=
      zNV _ (zxb (bzo k) (Ez k))
    ext z
    simp only [zeC,zyF,zw1 _ hinj]
  change zNo (zgt (aBg k)) (Ez (Ez k))
  rw [← hcomap]
  exact zHS M
    (zgt (aua k)) (Ez (Ez k)) (fun _ hu=>hu.mem_nonZeroDivisors)
private def aD9:Fin 4 ≃ Fin 2 ⊕ Fin 2 where
 toFun := ![zQG 0,znU 0,zQG 1,znU 1]
 invFun:=Sum.elim ![0,2] ![1,3]
 left_inv := by
  intro i
  fin_cases i <;> rfl
 right_inv := by
  rintro (i | i) <;> fin_cases i <;> rfl
private def polynomialEquiv (k :Type) [zrb k] :a96 k ≃+* aBg k :=
 ((zGY k aD9).trans (z3k k (Fin 2) (Fin 2))).toRingEquiv
private def cVK (k :Type) [zrb k] :
  zNv (a96 k) ≃+* Ez (Ez k) :=
 zDt (polynomialEquiv k)
private theorem b6C (k :Type) [zrb k] (x :a96 k) :
    cVK k (z12 (a96 k) (zNv (a96 k)) x) =
      z12 (aua k) (Ez (Ez k))
        (z12 (aBg k) (aua k) (polynomialEquiv k x)) := by
  rw [← zG3]
  exact zNB (polynomialEquiv k) x
private abbrev aFL:=Ez aQ
private abbrev alK:=cVK FX
private theorem dML (a :FX) :
   alK (z12 FX dV a) =
     z12 aQ aFL (z12 FX aQ a) := by
 change alK (z12 (a96 FX) dV (C a))= _
 rw [b6C]
 change z12 (aua FX) aFL
   (z12 (aBg FX) (aua FX) (z3k FX _ _ (zHw aD9 (C a))))= _
 rw [zt1,sumAlgEquiv_C_inl,zu8,zpw]
 rfl
private theorem cGv (i:Fin 2) :
  alK (kz (![0,2] i))=ahN aQ i:= by
 have hi:aD9 (![0,2] i)=zQG i:= by fin_cases i <;> rfl
 unfold kz ahN
 rw [b6C]
 change z12 (aua FX) aFL (z12 (aBg FX) (aua FX)
  (z3k FX _ _ (zHw aD9 (z9v (![0,2] i)))))= _
 rw [z6l,hi,zwY,zu8,z7N]
private theorem cGu (i:Fin 2) :
   alK (kz (![1,3] i)) =
     z12 aQ aFL (ek i) := by
 have hi:aD9 (![1,3] i)=znU i:= by fin_cases i <;> rfl
 unfold kz ek
 rw [b6C]
 change z12 (aua FX) aFL (z12 (aBg FX) (aua FX)
   (z3k FX _ _ (zHw aD9 (z9v (![1,3] i)))))= _
 rw [z6l,hi,zoo,zu8,zpw]
 rfl
private def ayQ:yT aQ →+* yT aFL :=
 zDK (z12 aQ aFL)
private def ako:PI →+* yT aFL :=
 zOD (C.comp alK.toRingHom)
  ![z9v (some 0),z9v (some 1),
    C (alK (kz 3)) - C (alK (kz 1))*z9v none,
    z9v none]
private theorem gu7:zpX ako:= by
 let includeFree :yT aFL →+* PI :=
   zOD (C.comp alK.symm.toRingHom)
     (fun i=>i.elim (z9v 3) (fun j=>z9v (![0,1] j)))
 have h:ako.comp includeFree=zz5 _:= by
   apply zXT
   · intro a
     simp [includeFree,ako]
   · rintro (_ | i)
     · simp [includeFree,ako]
     · fin_cases i <;> simp [includeFree,ako]
 intro p
 exact ⟨includeFree p,zmU h p⟩
private theorem gu5 :
   ako.comp AU=ayQ.comp Mv := by
 have h1 :=cGu 0
 have h3:=cGu 1
 change alK (kz 1)= _ at h1
 change alK (kz 3)= _ at h3
 apply zXT
 · intro a
   simp [ako,AU,ayQ,Mv,dML]
 · intro i
   fin_cases i <;> simp [ako,AU,ayQ,Mv,h1,h3]
private theorem gu6 (I:znc z87) :
  (I.map AU ⊔ zye {JN,Z6}).map ako =
    aP9 (RV I) := by
 have h0:=cGv 0
 have h2 :=cGv 1
 change alK (kz 0)= _ at h0
 change alK (kz 2)= _ at h2
 have hseed :ako JN =
    z9v (some 0)+C (ahN aQ 0)*z9v (some 1) - C (ahN aQ 1) := by
  simp [JN,ako,h0,h2]
 have hjet:ako Z6=0:= by
  simp [Z6,ako]
 simp [aP9,RV,← show ayQ =
  zDK (z12 aQ aFL) from rfl,
  zf9,zXe,zlN,zyl,
  z0L,gu5,hseed,hjet]
private theorem ea2 {F G M N :Type} [zrb F] [zrb G]
  [z2F M] [z2F N] [Module F M] [Module G N] [zAa F M]
  {σ:F →+* G} (l:M →ₛₗ[σ] N) (hl:zpX l) :
  zAa G N∧zsE G N≤zsE F M:= by
 refine ⟨zIU l hl,?_⟩
 let b:=Module.finBasis F M
 have hspan:zLD G (zxp (l ∘ b)) = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨x,rfl⟩:=hl y
  rw [Set.range_comp]
  exact zEE l _ ⟨x,by rw [b.span_eq]; trivial,rfl⟩
 simpa using zpS hspan
theorem proof :WJ.c2 := by
  intro I hfinite
  let _:=hfinite
  let J:=I.map AU ⊔ zye {JN,Z6}
  let J' := aP9 (RV I)
  have h:J≤J'.comap ako :=
    Ideal.map_le_iff_le_comap.mp (gu6 I).le
  let q:Ik I →+* W1 (RV I) :=z3G J' ako h
  let l:Ik I →ₛₗ[alK.toRingHom] W1 (RV I) :=
    { q.toAddMonoidHom with
      map_smul' := by
        intro a x
        change q (a•x)=alK a•q x
        rw [zd5 a x,zd5 (alK a) (q x),zok]
        congr 1
        change z3G J' ako h (zVv J (C a)) =
          zVv J' (C (alK a))
        rw [z5h]
        simp [ako] }
  have hl:zpX l:=Ideal.quotientMap_surjective (H :=h) gu7
  exact ea2 l hl
end
end czh
end
section
namespace bzW
noncomputable section
open gT WJ MM
open Polynomial
open scoped TensorProduct nonZeroDivisors
variable {k A:Type} [zrb k] [za6 A] [zZE k A]
abbrev aI2 (A:Type) [za6 A] :A[X] →+* zNv (A[X]) :=
 z12 _ _
private theorem gAX [ztn A] :
    ∃ g: (A ⊗[k] e7 k) →+* zNv (A[X]),
      zq4 g ∧
      (∀ a :A,g (a ⊗ₜ[k] 1)=aI2 A (C a)) ∧
      (∀ p:k[X],g (1 ⊗ₜ[k] z12 k[X] (e7 k) p) =
        aI2 A (p.map (z12 k A))) := by
  let P:=k[X]
  let M:=zgt P
  let R:=A ⊗[k] P
  let ι:P →ₐ[k] R:=zgi
  let S:=Localization (M.map ι)
  let e :A[X] ≃ₐ[A] R:=polyEquivTensor' k A
  let E :=IsLocalization.tensorProductEquivOfMapIncludeRight k A M (e7 k) S
  let j:=(aI2 A).comp e.symm.toRingHom
  have hj:zq4 j:=(zxb _ _).comp e.symm.injective
  have he (a :A) (p:P) :j (a ⊗ₜ[k] p) =
      aI2 A (C a*p.map (z12 k A)) := by
    change aI2 A ((polyEquivTensor k A).symm (a ⊗ₜ[k] p))= _
    rw [polyEquivTensor_symm_apply_tmul_eq_smul,zd5]
    rfl
  have hu : ∀ p:M.map ι,zWB (j p) := by
    rintro ⟨_,p,hp,rfl⟩
    change zWB (j (1 ⊗ₜ[k] p))
    rw [he,zXs,zkF]
    apply isUnit_iff_ne_zero.mpr
    exact (zw1 _ (zxb _ _)).mpr
      ((zeI (z12 k A).injective).mpr (zyw hp))
  let g:S →+* zNv (A[X]) :=zvq hu
  have hg (r :R) :g (z12 R S r)=j r :=zX4 _ _
  have hg_inj:zq4 g :=
    (zcf (S:=S) (hg:=hu)).mpr
      (fun x y=>⟨fun h=> by rw [← hg,← hg]; exact congrArg g h,
        fun h=>zPw (z12 R S) (hj h)⟩)
  refine ⟨g.comp E.toRingHom,hg_inj.comp E.injective,?_,?_⟩
  · intro a
    change g (E (a ⊗ₜ[k] (1 :e7 k)))= _
    rw [← zXs (z12 P (e7 k)),
      zL5,hg,he,
      Polynomial.map_one,zqg]
  · intro p
    change g (E ((1 :A) ⊗ₜ[k] z12 P (e7 k) p))= _
    rw [zL5,hg,he,zXs,zkF]
theorem gsF (D:znc (yT k)) [D.IsPrime] :
    let A:=gk D
    let L:=zNv (A[X])
    ∃ g:Cz D →+* L,
      zq4 g ∧
      (∀ f :yT k,g (auU D f) =
        aI2 A (C (zVv D f))) ∧
      (∀ p:k[X],g (z12 (e7 k) (Cz D)
          (z12 k[X] (e7 k) p)) =
        aI2 A (p.map (z12 k A))) := by
  dsimp only
  let A:=gk D
  let e : (A ⊗[k] e7 k) ≃+* Cz D :=
    (zOQ k A (e7 k)).toRingEquiv.trans
      (aXP D).toRingEquiv
  obtain ⟨g,hg,ha,hp⟩:=gAX (k :=k) (A:=A)
  refine ⟨g.comp e.symm.toRingHom,?_,?_,?_⟩
  · change zq4 (fun x=>g (e.symm x))
    exact hg.comp e.symm.injective
  · intro f
    have he :e (zVv D f ⊗ₜ[k] (1 :e7 k))=auU D f := by
      change aXP D (zOQ k A (e7 k)
        (zVv D f ⊗ₜ[k] (1 :e7 k)))= _
      rw [zrc]
      exact deB D f
    rw [← he]
    change g (e.symm (e _))= _
    rw [zp4]
    exact ha _
  · intro p
    have he :e (1 ⊗ₜ[k] z12 k[X] (e7 k) p) =
      z12 (e7 k) (Cz D) (z12 k[X] (e7 k) p) := by
      change aXP D (zOQ k A (e7 k)
        (1 ⊗ₜ[k] z12 k[X] (e7 k) p))= _
      rw [zrc]
      exact (aXP D).commutes _
    rw [← he]
    change g (e.symm (e _))= _
    rw [zp4]
    exact hp _
end
end bzW
end
section
set_option backward.isDefEq.respectTransparency false
namespace czi
noncomputable section
open cu gT pI WJ MvPolynomial
open scoped TensorProduct
private abbrev Parameters (k :Type) [zrb k] :=z3y (Fin 2) k
private abbrev sU (k :Type) [zrb k] :=zNv (Parameters k)
private def aon (k :Type) [zrb k] :Parameters k →+* zM1 (Parameters k) :=
 zOD (Polynomial.C.comp znf)
  ![z1z (z9v 1)-Polynomial.C (z9v 0)*z7y,
    z7y]
private theorem epU (k :Type) [zrb k] :
   zq4 (aon k) := by
 let s :Parameters k →+* Parameters k :=zOD znf ![0,z9v 0]
 let r :zM1 (Parameters k) →+* Parameters k :=zqf s (z9v 1)
 have hr :r.comp (aon k)=zz5 _:= by
   apply zXT
   · intro a
     simp [r,s,aon,zQb]
   · intro i
     fin_cases i <;> simp [r,s,aon]
 exact Function.LeftInverse.injective (g:=r) (fun p=>zLs hr p)
private def brk (k :Type) [zrb k] :
   Parameters k →+* JU (sU k) :=
 (z12 (zM1 (sU k)) (JU (sU k))).comp
   ((zhd (z12 (Parameters k) (sU k))).comp (aon k))
private theorem epT (k :Type) [zrb k] :
  zq4 (brk k) := by
 change zq4
  (z12 (zM1 (sU k)) (JU (sU k)) ∘
    zGG (z12 (Parameters k) (sU k)) ∘ aon k)
 exact (zxb _ _).comp
  ((zTo _ (zxb _ _)).comp (epU k))
private def al9 (k :Type) [zrb k] :
  sU k →+* JU (sU k) :=
 zIj (epT k)
private theorem b6F (k :Type) [zrb k] (q:Parameters k) :
  al9 k (z12 (Parameters k) (sU k) q) =
   brk k q :=
 zoc _ q
private theorem epx (k :Type) [zrb k] (a :k) :
   al9 k (z12 k (sU k) a) =
     z12 (sU k) (JU (sU k)) (z12 k (sU k) a) := by
 change al9 k (z12 (Parameters k) (sU k) (znf a))= _
 rw [b6F]
 simp only [brk,zQb,aon,zTv,
   zKC,zrL]
 exact (zG3 (sU k) (zM1 (sU k))
   (JU (sU k)) (z12 k (sU k) a)).symm
private theorem dL4 (k :Type) [zrb k] (a :sU k) :
   z12 (zM1 (sU k)) (JU (sU k)) (z1z a) =
     z12 (sU k) (JU (sU k)) a :=
 (zG3 (sU k) (zM1 (sU k))
   (JU (sU k)) a).symm
private theorem epV (k :Type) [zrb k] :
  aon k (z9v 0) =
   z1z (z9v 1)-Polynomial.C (z9v 0)*Polynomial.X:= by
 simp [aon]
private theorem epz (k :Type) [zrb k] :
   al9 k (z12 (Parameters k) (sU k) (z9v 1)) =
     z12 (zM1 (sU k)) (JU (sU k)) Polynomial.X:= by
 rw [b6F]
 simp [brk,aon]
private theorem b8z {R S F A:Type} [za6 R] [za6 S] [za6 F] [za6 A]
  (m:R →+* S) (j:zM1 S →+* F) (i:S →+* F) (c:F →+* A)
  (hi : ∀ x,j (z1z x)=i x) (t b:R) :
  c (i (m b)) - c (i (m t))*c (j z7y) =
    c (j (zGG m (z1z b-Polynomial.C t*z7y))) := by
 simp only [Polynomial.map_sub,Polynomial.map_mul,zrL,zSo,
  zpO,zok,hi]
private theorem grU :
   (awP aQ).comp Mv =
     (zDK (al9 FX)).comp CG:= by
 apply zXT
 · intro a
   simp [zQb,awP,Mv,CG,epx]
 · intro i
   fin_cases i <;>
     simp [zQb,awP,Mv,CG,ek,epz]
   simp only [b6F,brk,zQb,
     zKC,epV]
   exact b8z (z12 aZ aQ)
     (z12 (zM1 aQ) (JU aQ))
     (z12 aQ (JU aQ)) znf (dL4 FX)
     (z9v 0) (z9v 1)
private theorem To (I:znc z87) :
   (RV I).map (awP aQ) =
     (I.map CG).map (zDK (al9 FX)) := by
 rw [RV,z0L,z0L,grU]
private def d5v {k E σ:Type} [zrb k] [zrb E] [zZE k E]
    (J:znc (z3y σ k)) :
    E ⊗[k] gk J ≃ₐ[E]
      gk (J.map (zDK (z12 k E))) := by
  let e :E ⊗[k] z3y σ k ≃ₐ[E] z3y σ E :=
    zoR k E
  have he : (e :E ⊗[k] z3y σ k →+* z3y σ E).comp
      (zgi (R:=k) (A:=E) (B:=z3y σ k) :
        z3y σ k →+* E ⊗[k] z3y σ k) =
      zDK (z12 k E) := by
    apply zz4
    intro p
    change e (1 ⊗ₜ[k] p)= _
    simp [e]
  refine (zTd (R:=k) E (z3y σ k) E J).trans
    (zpY _ _ e ?_)
  rw [← he,← z0L]
  rfl
private theorem d5D {k E σ:Type} [zrb k] [zrb E] [zZE k E]
   (J:znc (z3y σ k)) [zAa k (gk J)] :
   zAa E (gk (J.map (zDK (z12 k E)))) ∧
   zsE E (gk (J.map (zDK (z12 k E)))) =
     zsE k (gk J) := by
 let e :=(d5v (E :=E) J).toLinearEquiv
 exact ⟨zIU e.toLinearMap e.surjective,
   e.finrank_eq.symm.trans zXY⟩
theorem proof :WJ.c3:= by
 intro I hI
 let:zZE aQ (JU aQ) :=(al9 FX).toAlgebra
 obtain ⟨hfinite,hrank⟩:=d5D (E :=JU aQ) (I.map CG)
 change zAa (JU aQ) (gk ((RV I).map (awP aQ))) ∧
   zsE (JU aQ) (gk ((RV I).map (awP aQ))) ≤
     zsE aQ (Lj I)
 rw [To]
 exact ⟨hfinite,hrank.le⟩
end
end czi
end
section
set_option maxHeartbeats 500000
namespace czc
noncomputable section
open cu gT pI ac4 MvPolynomial
open scoped nonZeroDivisors TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev ajc:=CS aQ
private abbrev cAs :=z3y (Fin 4) ajc
private abbrev DT:=z3y (Fin 4) FX
private abbrev aKG:=z3y (Fin 2) aZ
private abbrev aSb:=z3y (Fin 2) aQ
private def indices :Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
 (zFe 1 2).trans (ziU (m:=2) (n:=2)).symm
private def nest (k :Type) [zrb k] :
   z3y (Fin 4) k ≃+* z3y (Fin 2) (z3y (Fin 2) k) :=
 ((zGY k indices).trans (z3k k (Fin 2) (Fin 2))).toRingEquiv
private theorem cGG (k :Type) [zrb k] :
    ∃ e :RingEquiv (zNv (z3y (Fin 4) k)) (CS (CS k)),
      ∀ p:z3y (Fin 4) k,
        e (z12 (z3y (Fin 4) k) (zNv (z3y (Fin 4) k)) p) =
          z12 (z3y (Fin 2) (CS k)) (CS (CS k))
            (z12 (z3y (Fin 2) (z3y (Fin 2) k))
              (z3y (Fin 2) (CS k)) (nest k p)) := by
  let P:=z3y (Fin 2) k
  let H :=zNv P
  let B:=z3y (Fin 4) k
  let N :=z3y (Fin 2) P
  let S:=z3y (Fin 2) H
  let F:=zNv B
  let T:=zNv S
  let D:zdT N :=P⁰.map znf
  have :zNo D S:=zEY P⁰ H
  have hinj:zq4 (z12 N S) :=
    zNV _ (zxb P H)
  have hcomap :S⁰.comap (z12 N S)=N⁰:= by
    ext x
    simp only [zeC,zyF,zw1 _ hinj]
  have :z0o N T:= by
    change zNo N⁰ T
    rw [← hcomap]
    exact zHS D
      S⁰ T (fun _ hu=>hu.mem_nonZeroDivisors)
  let s :B ≃+* N :=nest k
  let e :F ≃+* T:=zDt s
  refine ⟨e,fun p => ?_⟩
  change e (z12 B F p)=z12 S T (z12 N S (s p))
  rw [← zG3 N S T]
  exact zNB s p
private def coefficients :RingEquiv dV ajc :=
 (cGG FX).choose
private theorem bX5 (p:DT) :
   coefficients (z12 DT dV p) =
    z12 aSb ajc (z12 aKG aSb (nest FX p)) :=
 (cGG FX).choose_spec p
private theorem dM9 (x :FX) :
   coefficients (z12 FX dV x) =
     z12 aQ ajc (z12 FX aQ x) := by
 change coefficients (z12 DT dV (C x))= _
 rw [bX5]
 change z12 aSb ajc
   (z12 aKG aSb (z3k _ _ _ (zGY FX indices (C x))))= _
 rw [zyk,zt1,sumAlgEquiv_C_inl,zu8,zpw]
 rfl
private theorem bX6 {i:Fin 4} {j:Fin 2} (h:indices i=zQG j) :
  coefficients (kz i)=arW aQ j:= by
 rw [kz,bX5]
 change z12 aSb ajc
  (z12 aKG aSb (z3k _ _ _ (zGY FX indices (z9v i))))= _
 rw [zyk,z6l,h,zwY,
  zu8,z7N]
 rfl
private theorem dM8 {i:Fin 4} {j:Fin 2} (h:indices i=znU j) :
  coefficients (kz i)=z12 aQ ajc (ek j) := by
 rw [kz,bX5]
 change z12 aSb ajc
  (z12 aKG aSb (z3k _ _ _ (zGY FX indices (z9v i))))= _
 rw [zyk,z6l,h,zoo,
  zu8,zpw]
 rfl
private def afd:PI ≃+* cAs :=
 zuz (Fin 4) coefficients
private theorem ds3 :
   afd.toRingHom.comp AU=(Cl aQ).comp (Cl FX) := by
 apply zXT
 · intro x
   simp only [zQb,AU,Cl,zpw]
   change afd (C (z12 FX dV x)) =
    C (z12 aQ ajc (z12 FX aQ x))
   rw [afd,zut,zpw]
   exact zPw C (dM9 x)
 · intro i
   simp [afd,AU,Cl]
private theorem eHP :
  afd (z9v 2 - C (kz 3))=Cl aQ (Pp 2) := by
 have hy :=dM8 (i:=3) (j:=1) rfl
 simp [afd,zut,Cl,Pp,hy]
private theorem gn6 :
  afd JN =
   z9v 0+C (arW aQ 0)*z9v 1 - C (arW aQ 1) := by
 have hs :=bX6 (i:=0) (j:=0) rfl
 have ht:=bX6 (i:=2) (j:=1) rfl
 simp [afd,zut,JN,hs,ht]
private theorem dWr :
  afd (z9v 3 - C (kz 2))=z9v 3 - C (arW aQ 1) := by
 have hv :=bX6 (i:=2) (j:=1) rfl
 simp [afd,zut,hv]
private def aHV (I:znc z87) (cut:PI) :znc PI :=
 I.map AU ⊔ zye {cut,z9v 2 - C (kz 3)}
private theorem cSD (I:znc z87) (cut:PI) :
   (aHV I cut).map afd.toRingHom =
     (Hr I).map (Cl aQ) ⊔ zye {afd cut} := by
 simp only [aHV,Hr,zf9,zXe,zlN,
   zyl,z0L,ds3]
 rw [show afd.toRingHom (z9v 2 - C (kz 3)) =
   Cl aQ (Pp 2) from eHP]
 let J:=I.map ((Cl aQ).comp (Cl FX))
 let A:=zye {afd cut}
 let B:=zye {Cl aQ (Pp 2)}
 change J ⊔ (A ⊔ B)=(J ⊔ B) ⊔ A
 rw [sup_assoc,sup_comm B A]
private theorem transport {J:znc PI} {J' : znc cAs}
    (hJ:J' = J.map afd.toRingHom)
    (hfinite :zAa dV (gk J)) :
    zAa ajc (gk J') ∧
      zsE ajc (gk J') =
        zsE dV (gk J) := by
  let e :=Ideal.quotientEquiv J J' afd hJ
  have hcomm :
      (z12 ajc (gk J')).comp coefficients.toRingHom =
        e.toRingHom.comp (z12 dV (gk J)) := by
    apply zz4
    intro x
    change zVv J' (C (coefficients x)) =
      zVv J' (afd (C x))
    rw [afd,zut,zpw]
    rfl
  let f :gk J →ₛₗ[coefficients.toRingHom] gk J' :=
    { toFun:=e
      map_add' := e.map_add
      map_smul' := fun c x=> by
        have hc:=zLs hcomm c
        simp only [zQb] at hc
        calc
          e (c•x)=e (z12 dV (gk J) c*x) :=
            zPw e (zd5 c x)
          _=e (z12 dV (gk J) c)*e x :=e.map_mul _ _
          _=z12 ajc (gk J') (coefficients.toRingHom c)*e x :=
            zPw (fun y=>y*e x) hc.symm
          _=coefficients.toRingHom c•e x :=(zd5 _ _).symm }
  let _:=hfinite
  exact ⟨zIU f e.surjective,
    (znu coefficients e hcomm).symm⟩
private theorem goZ (I:znc z87)
    (hfinite :zAa dV (ani I)) :
    zAa ajc (W1 (Hr I)) ∧
      zsE ajc (W1 (Hr I)) =
        zsE dV (ani I) := by
  apply transport (J:=aHV I JN) _ hfinite
  rw [cSD,gn6]
private def bHZ:Fin 2→Fin 4 :=
 zFe 2 3 ∘ zzs 2
private def al9:aQ →+* dV :=
 zJ1 (K:=aQ) (L:=dV)
  (j:=(zHw (R:=FX) bHZ).toRingHom)
  (zLm _ ((zFe 2 3).injective.comp (Fin.natAdd_injective 2 2)))
private theorem epw (i:Fin 2) :
  al9 (ek i)=kz (bHZ i) := by
 unfold al9 ek kz zJ1
 rw [zi7]
 simp
private theorem epy (x :FX) :
  al9 (z12 FX aQ x)=z12 FX dV x := by
 change al9 (z12 aZ aQ (C x)) =
  z12 DT dV (C x)
 unfold al9 zJ1
 rw [zi7]
 simp
private def yZ:PI →ₐ[dV] z3y (Fin 2) dV :=
 zIe ![z9v 0,z9v 1,C (kz 3),C (kz 2)]
private def AH :z3y (Fin 2) dV →ₐ[dV] PI :=
 zHw (zVs 2)
private theorem cVP:zpX yZ:= by
 have he :yZ.comp AH=zhD _ _:= by
  apply zpH
  intro i
  fin_cases i <;> simp [yZ,AH]
 intro p
 exact ⟨AH p,zmU he p⟩
private def adP:PI:=z9v 3 - C (kz 2)
private theorem epJ :
   zdq yZ.toRingHom=zye {adP,z9v 2 - C (kz 3)} := by
 let J:znc PI:=zye {adP,z9v 2 - C (kz 3)}
 let q:=zvR dV J
 have hy :q (z9v 2)=q (C (kz 3)) := by
   apply sub_eq_zero.mp
   rw [← zpO]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (zCn (by simp))
 have hv :q (z9v 3)=q (C (kz 2)) := by
   apply sub_eq_zero.mp
   rw [← zpO]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (zCn (by simp [adP]))
 have he : (q.comp AH).comp yZ=q:= by
   apply zpH
   intro i
   fin_cases i <;> simp [yZ,AH,algHom_C,hy,hv]
 apply zWs
 · intro p hp
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   change q p=0
   rw [← zmU he p]
   change q (AH (yZ p))=0
   rw [show yZ p=0 from hp,zhc,zhc]
 · apply Ideal.span_le.mpr
   intro p hp
   change p∈({adP,z9v 2 - C (kz 3)} : Set PI) at hp
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
   rcases hp with rfl | rfl <;> simp [zry,adP,yZ,zKm]
private theorem epH :
   yZ.toRingHom.comp AU=(zDK al9).comp CG:= by
 apply zXT
 · intro x
   simp [yZ,AU,CG,zKm,epy]
 · intro i
   have h₀:bHZ 0=3:=rfl
   have h₁:bHZ 1=2 :=rfl
   fin_cases i <;> simp [yZ,AU,CG,epw,h₀,h₁]
section BaseChange
variable {k L σ:Type*} [zrb k] [zrb L] [zZE k L]
private def d5C (I:znc (z3y σ k)) :
   L ⊗[k] (z3y σ k ⧸ I) ≃ₐ[L]
     z3y σ L ⧸ I.map (zDK (z12 k L)) := by
 let e :=zoR (σ:=σ) k L
 refine (zTd L (z3y σ k) L I).trans
   (zpY _ _ e ?_)
 change I.map (zDK (z12 k L)) =
   (I.map (zgi (A:=L)).toRingHom).map
     e.toRingEquiv.toRingHom
 rw [z0L]
 congr 1
 apply zz4
 intro p
 change zDK (z12 k L) p=e (1 ⊗ₜ[k] p)
 simp [e]
end BaseChange
private theorem ec8 (I:znc z87)
    (hfinite :zAa aQ (Lj I)) :
    zAa dV (gk (aHV I adP)) ∧
      zsE dV (gk (aHV I adP)) =
        zsE aQ (Lj I) := by
  let:zZE aQ dV:=al9.toAlgebra
  let J:znc (z3y (Fin 2) dV) :=
    (I.map CG).map (zDK al9)
  let f :=(zvR dV J).comp yZ
  have hmap : (I.map AU).map yZ.toRingHom=J:= by
    dsimp only [J]
    rw [z0L,z0L,epH]
  have hker :zdq f.toRingHom=aHV I adP:= by
    change zK3 yZ.toRingHom (zdq (zVv J))= _
    have hsurj:zpX yZ.toRingHom:=cVP
    rw [zlC,← hmap,zEk _ hsurj,
      ← zPx,epJ]
    rfl
  let e :gk (aHV I adP) ≃ₐ[dV] gk J :=
    (z9k dV hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f :=f)
        (Ideal.Quotient.mk_surjective.comp cVP))
  let t:dV ⊗[aQ] Lj I ≃ₐ[dV] gk J :=
    d5C (I.map CG)
  let u:=(t.trans e.symm).toLinearEquiv
  let _:=hfinite
  refine ⟨zIU u.toLinearMap u.surjective,?_⟩
  rw [← u.finrank_eq,zXY]
private theorem dWu (I:znc z87)
    (hfinite :zAa aQ (Lj I)) :
    zAa ajc (adm (Hr I)) ∧
      zsE ajc (adm (Hr I)) =
        zsE aQ (Lj I) := by
  obtain ⟨hf,hr⟩:=ec8 I hfinite
  have hm: (Hr I).map (Cl aQ) ⊔
      zye {z9v 3 - C (arW aQ 1)} =
      (aHV I adP).map afd.toRingHom:= by
    rw [cSD,adP,dWr]
  obtain ⟨h,r⟩:=transport hm hf
  exact ⟨h,r.trans hr⟩
theorem proof :ac4.c2 := by
 intro I ho hj
 obtain ⟨hs,rs⟩:=goZ I ho
 obtain ⟨hv,rv⟩:=dWu I hj
 exact ⟨hs,hv,rs,rv⟩
end
end czc
end
section
set_option backward.isDefEq.respectTransparency false
namespace baC
noncomputable section
open MM IsDedekindDomain IsLocalRing WithZero
open UniqueFactorizationMonoid
open scoped Classical WithZero
variable {F B K:Type} [zrb F] [za6 B] [zJZ B] [zrb K]
 [zZE F B] [zZE F K] [zZE B K] [zsf F B K] [z0o B K]
private def bbG (p:zZx B) :zZ F K :=
 ⟨p.valuation K,p.valuation_surjective K,(Valuation.IsTrivialOn.of_le_one
   (p.valuation K) fun c=> by
     rw [zG3 F B K]
     exact p.valuation_le_one (z12 F B c)).eq_one⟩
private theorem dsf :zq4 (bbG (F:=F) (K:=K) (B:=B)) :=
 fun _ _ h=>zPZ K (zPw zZ.val h)
private theorem dsg (p:zZx B) {b:B} (hb:b≠0) :
  KB (bbG (F:=F) (K:=K) p) (z12 B K b) =
   zug p.asIdeal (zye {b}) := by
 change (-log (p.valuation K (z12 B K b))).toNat= _
 simp only [p.valuation_of_algebraMap,p.intValuation_eq_exp_neg_multiplicity hb,
  zOL,neg_neg,zQf]
private theorem eOg [zUK F B] (p:zZx B) (n:ℕ) :
    zsE F (B ⧸ p.asIdeal^n) =
      n*QZ (bbG (F:=F) (K:=K) p) := by
  let w:=bbG (F:=F) (K:=K) p
  let V:=w.val.valuationSubring
  let:zZE B V:=((z12 B K).codRestrict V.toSubring
    (p.valuation_le_one (K:=K))).toAlgebra
  let:zsf F B V:=zsL fun c=> by
    apply zkt
    exact zG3 F B K c
  let e :p.valuationSubringAtPrime K ≃ₐ[B] V :=
    { zh4 (zPw zJ2
        (p.valuationSubringAtPrime_eq_valuationSubring (K:=K))) with
      commutes' := fun _=>zkt rfl }
  let:zNo p.asIdeal.primeCompl V :=
    zfY p.asIdeal.primeCompl e
  let:z8E V :=
    zx9 B p.ne_bot V
  let:p.asIdeal.IsMaximal:=p.isMaximal
  let q (j:ℕ) :=(zYv p.asIdeal V j).restrictScalars F
  let qres : (B ⧸ p.asIdeal) ≃ₐ[F] zhZ V :=
    (z9k F (pow_one p.asIdeal).symm).trans
      ((q 1).trans (z9k F (pow_one (zrY V))))
  let:zAa F (B ⧸ p.asIdeal) :=z3E p.asIdeal p.ne_bot
  let:zAa F (zhZ V) :=zZc qres.toLinearEquiv
  let:zAa F (B ⧸ p.asIdeal^n) :=z3E _ (zm1 _ p.ne_bot)
  let:zAa F (V ⧸ zrY V^n) :=zZc (q n).toLinearEquiv
  have hres :zKQ (zhZ F) (zhZ V) =
      zsE F (zhZ V) := by
    rw [← zAi (R:=zhZ F)
      (z6A (R:=F)),z1C]
  have hlen:=z9y F V (V ⧸ zrY V^n)
  rw [z1C,zRe,hres] at hlen
  change zsE F (B ⧸ p.asIdeal^n)=n*zsE F (zhZ V)
  rw [(q n).toLinearEquiv.finrank_eq]
  exact_mod_cast hlen
private abbrev apX (I:znc B) :=(factors I).toFinset
private def aUx {I:znc B} (p:apX I) :zZx B :=
 HeightOneSpectrum.ofPrime (prime_of_factor p.val (Multiset.mem_toFinset.mp p.property))
theorem eFq [zUK F B] (b:B) (hb:b≠0) :
    ∃ S:zJe (zZ F K),
      zsE F (B ⧸ zye {b})=aAJ S (z12 B K b) := by
  let I:=zye {b}
  have hI:I ≠ ⊥ := by simpa only [I,ne_eq,Ideal.span_singleton_eq_bot] using hb
  let n (p:apX I) :=(factors I).count p.val
  let e :=zsT hI
  let eF: (B ⧸ I) ≃ₐ[F] ∀ p:apX I,B ⧸ p.val^n p :=
    { e with
      commutes' := fun c=> by
        funext p
        change e (zVv _ (z12 F B c)) p =
          zVv _ (z12 F B c)
        rw [znh] }
  let w:apX I ↪ zZ F K :=
    ⟨fun p=>bbG (aUx p),fun _ _ h =>
      zkt (zPw HeightOneSpectrum.asIdeal (dsf h))⟩
  refine ⟨Finset.univ.map w,?_⟩
  have (p:apX I) :zAa F (B ⧸ p.val^n p) :=
    z3E _ (zm1 _ (aUx p).ne_bot)
  rw [eF.toLinearEquiv.finrank_eq,z0r,aAJ,z93]
  apply zUo rfl
  intro p _
  have hn:KB (w p) (z12 B K b)=n p:= by
    rw [show w p=bbG (aUx p) from rfl,dsg _ hb]
    change zug (aUx p).asIdeal I=(factors I).count (aUx p).asIdeal
    rw [zy7,zwP hI]
  rw [hn,zDE]
  exact eOg (F:=F) (K:=K) (aUx p) (n p)
end
end baC
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace czb
noncomputable section
open cu gT pI ac4
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem ev9
    {R S:Type} [za6 R] [za6 S] [zZE R S]
    [zVK R S] [znE R S] (l:zDY (zy6 R)) :
    ∃ L:zDY (zy6 S),
      L.length=l.length∧L.last.asIdeal.under R=l.last.asIdeal:= by
  induction l using zvN with
  | singleton p =>
    have :=p.isPrime
    have hle : (⊥ : znc S).under R≤p.asIdeal:= by
      change zK3 (z12 R S) ⊥ ≤ p.asIdeal
      rw [← zPx,
        (zli _).mp (zJj R S)]
      exact bot_le
    obtain ⟨P,_,hP,hPp⟩:=zuu
      p.asIdeal (⊥ : znc S) hle
    exact ⟨zYY _ ⟨P,hP⟩,rfl,hPp⟩
  | snoc l p hp ih =>
    obtain ⟨L,hlen,hlast⟩:=ih
    have :=p.isPrime
    have hlt:l.last<p:=hp
    obtain ⟨P,hLP,hP,hPp⟩:=zuu
      p.asIdeal L.last.asIdeal (hlast.trans_le hlt.le)
    have hnext:L.last<(⟨P,hP⟩:zy6 S) := by
      refine zXi hLP fun heq=>hlt.ne (PrimeSpectrum.ext_iff.mpr ?_)
      exact hlast.symm.trans ((zPw (fun x :zy6 S=>x.asIdeal.under R) heq).trans hPp)
    exact ⟨L.snoc ⟨P,hP⟩ hnext,by simp [RelSeries.snoc,hlen],by simpa using hPp⟩
private theorem aSS (k A:Type) [zrb k] [za6 A] [ztn A]
   [zZE k A] [zUK k A] :
   ∃ d:ℕ,zqe A=(d:zUi ℕ∞)∧zls k A=(d:zpf) := by
 obtain ⟨d,g,hginj,hgfin⟩:=z4J k A
 let R:=z3y (Fin d) k
 let:zZE R A:=g.toRingHom.toAlgebra
 let:zAa R A:=hgfin
 let:zVK R A:=zux R A
 let:znE R A:=(zSO R A).mpr hginj
 let:zsf k R A:=zsL fun a=>(g.commutes a).symm
 have hdim:zqe R=(d:zUi ℕ∞) := by
   simp [R,zmx,zZT]
 refine ⟨d,?_,?_⟩
 · rw [← hdim]
   apply zWs
   · apply zol (zRL (z12 R A))
     intro a b hab
     exact zu9 (R:=R) (show a.asIdeal<b.asIdeal from hab)
   · rw [hdim]
     obtain ⟨l,hlen⟩:=Order.le_krullDim_iff.mp hdim.ge
     obtain ⟨L,hL,_⟩:=ev9 (S:=A) l
     exact Order.le_krullDim_iff.mpr ⟨L,hL.trans hlen⟩
 · let:zjH R A:=Algebra.IsAlgebraic.of_finite R A
   simpa [R,zBT (R:=R) (A:=A),zUc] using
     (z5k (A:=A) k R).symm
private abbrev Lg:=z3y (Fin 4) aZ
private abbrev Ek :zdT Lg :=
 aZ⁰.map (znf (σ:=Fin 4))
private def CV:z87 →+* Lg :=
 zDK znf
private def blS:Lg :=
 z9v 2 - znf (z9v 1)
private def pD (I:znc z87) :aZ →+* zM1 (gk I) :=
 zOD (Polynomial.C.comp ((zVv I).comp znf))
  ![z7y,z1z (zVv I (z9v 2))]
private def wW (I:znc z87) :Lg →+* zM1 (gk I) :=
 zOD (pD I)
  (fun i=>z1z (zVv I (z9v i)))
private theorem ax8 (I:znc z87) :
   (wW I).comp CV=Polynomial.C.comp (zVv I) := by
 apply zXT
 · intro a
   simp [wW,CV,pD]
 · intro i
   simp [wW,CV]
private theorem a1C (I:znc z87) :zpX (wW I) := by
  let u:=zqf CV
    (znf (z9v 0) :Lg)
  have he : (wW I).comp u=zhd (zVv I) := by
    apply z86
    · intro a
      simp only [zQb,u,z4Q,zJU,
        zKC,zrL]
      exact zLs (ax8 I) a
    · simp [u,wW,pD]
  have hs :zpX ((wW I).comp u) := by
    rw [he]
    exact zMr _ zld
  exact Function.Surjective.of_comp (f :=wW I) (g:=u) hs
private theorem bfm :
   (z12 Lg aiS).comp CV=Cl FX:= by
 change (zDK (z12 aZ aQ)).comp CV=Cl FX
 apply zXT
 · intro a
   simp only [zQb,CV,Cl,zpw]
   rfl
 · intro i
   simp only [zQb,CV,Cl,z7N]
private theorem exW :
  z12 Lg aiS blS=Pp 2 := by
 change zDK (z12 aZ aQ) blS=Pp 2
 simp only [blS,zpO,z7N,zpw,Pp,ek]
private abbrev Gl (I:znc z87) :=gk (Hr I)
private def c5Y (I:znc z87) :gk I →+* Gl I :=
 zP2 I ((zVv (Hr I)).comp (Cl FX))
  (fun _ ha=>Ideal.Quotient.eq_zero_iff_mem.mpr
    (zKg (z7X (Cl FX) ha)))
private def arZ (I:znc z87) :zM1 (gk I) →+* Gl I :=
 zqf (c5Y I)
  (zVv (Hr I) (znf (ek 0)))
private theorem bKD (I:znc z87) (a :z87) :
  arZ I (z1z (zVv I a)) =
   zVv (Hr I) (Cl FX a) := by
 simp only [arZ,z4Q,zJU,c5Y,
  z0R]
 rfl
private theorem eH2 (I:znc z87) :
   zVv (Hr I) (z9v 2) =
     zVv (Hr I) (znf (ek 1)) := by
 apply sub_eq_zero.mp
 rw [← zpO,z1Q]
 exact zs0 (zCn (zT1 (Pp 2)))
private theorem b19 (I:znc z87) :
    (zVv (Hr I)).comp (z12 Lg aiS) =
      (arZ I).comp (wW I) := by
  let q:=zVv (Hr I)
  let f :Lg →+* aiS:=zDK (z12 aZ aQ)
  change q.comp f=(arZ I).comp (wW I)
  apply zXT
  · have hc: (q.comp f).comp znf =
        ((arZ I).comp (wW I)).comp MvPolynomial.C:= by
      apply zXT
      · intro a
        change q (f (znf (znf a))) =
          arZ I (wW I (znf (znf a)))
        simp only [f,zpw,wW,pD,zTv,
          zQb,bKD,Cl]
        rfl
      · intro i
        change q (f (znf (z9v i))) =
          arZ I (wW I (znf (z9v i)))
        simp only [f,zpw,wW,zTv,pD,
          zrD]
        fin_cases i
        · change q (znf (ek 0))=arZ I z7y
          simp only [arZ,z4Q,zC9,q]
        · change q (znf (ek 1)) =
            arZ I (z1z (zVv I (z9v 2)))
          rw [bKD,Cl,z7N]
          exact (eH2 I).symm
    exact zLs hc
  · intro i
    change q (f (z9v i))=arZ I (wW I (z9v i))
    simp only [f,z7N,wW,zrD,bKD,
      Cl,q]
private abbrev aXs (I:znc z87) :
   zZE (zM1 (gk I)) (Gl I) :=
 (arZ I).toAlgebra
private theorem exS (I:znc z87) :
    letI:zZE (zM1 (gk I)) (Gl I) :=aXs I
    zNo (Ek.map (wW I)) (Gl I) := by
  let:zZE (zM1 (gk I)) (Gl I) :=aXs I
  apply IsLocalization.of_surjective (S' := Gl I) Ek aiS (wW I)
    (a1C I) (zVv (Hr I)) zld
    (b19 I)
  rw [zlC,Hr]
  apply zbX
  · rw [← bfm,← z0L]
    apply zi2
    rw [zo0]
    intro a ha
    change wW I (CV a)=0
    rw [show wW I (CV a)=z1z (zVv I a)
        from zLs (ax8 I) a,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha,zhc]
  · rw [← exW,zvl]
    apply z7X
    change wW I blS=0
    simp [wW,blS,pD]
private theorem gnE (I:znc z87) (a :FX) :
   z12 FX (Gl I) a =
     arZ I (z12 FX (zM1 (gk I)) a) := by
 change zVv (Hr I) (znf (z12 FX aQ a)) =
   arZ I (z1z (zVv I (znf a)))
 rw [bKD,Cl,zpw]
private theorem ct6 (k R S:Type) [zrb k] [za6 R] [za6 S]
  [ztn R] [ztn S] [zZE k R] [zZE k S] [hAlg:zZE R S]
  [znE k R] (M:zdT R) [hLoc:zNo M S]
  (hcomp : ∀ x :k,z12 k S x=z12 R S (z12 k R x)) :
  zls k S=zls k R:= by
 let:zsf k R S:=zsL hcomp
 have hM:M≤R⁰:= by
  intro a ha
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  have hunit :=z0j S (⟨a,ha⟩:M)
  change zWB (z12 R S a) at hunit
  rw [h,zhc] at hunit
  exact not_isUnit_zero hunit
 let:znE R S:=(zSO R S).mpr
  (IsLocalization.injective S hM)
 let:zjH R S:=zyQ S M
 simpa only [zBT (R:=R) (A:=S),z0a] using
  (z5k (A:=S) k R).symm
private theorem ct8 (k R:Type) [zrb k] [za6 R] [ztn R]
  [zZE k R] [znE k R] :
  zls k (zM1 R)=zls k R+1 := by
 let:znE R (zM1 R) :=(zSO R (zM1 R)).mpr
  zmy
 simpa only [zBA] using (z5k (A:=zM1 R) k R).symm
private theorem ct9 (I:znc z87) (hp:I.IsPrime)
   (hdom:zq4 ((zVv I).comp F7)) :
   zls FX (Gl I)=zls FX (gk I)+1 := by
 let:=hp
 let: (Hr I).IsPrime :=((btg I hp).1 hdom).1
 let:znE FX (zM1 (gk I)) :=
   (zSO FX (zM1 (gk I))).mpr
     (z12 FX (zM1 (gk I))).injective
 let:znE FX (gk I) :=
   (zSO FX (gk I)).mpr
     (z12 FX (gk I)).injective
 have hloc:=ct6 FX (zM1 (gk I)) (Gl I)
   (hAlg:=aXs I) (Ek.map (wW I))
   (hLoc:=exS I) (gnE I)
 exact hloc.trans (ct8 FX (gk I))
private theorem cua :zls FX aQ=2 := by
 let:zjH aZ aQ:=zyQ aQ aZ⁰
 simpa [aZ,zBT (R:=aZ) (A:=aQ),zUc] using
  (z5k (A:=aQ) FX aZ).symm
theorem proof :ac4.c1 := by
 intro I hp hdim hdom
 change zqe (Gl I)=1
 let:=hp
 let: (Hr I).IsPrime :=((btg I hp).1 hdom).1
 obtain ⟨d,hd,ht⟩:=aSS FX (gk I)
 have hd' : d = 2 := by
   rw [hdim] at hd
   exact_mod_cast hd.symm
 have htotal:zls FX (Gl I)=3:= by
   rw [ct9 I hp hdom,ht,hd']
   norm_num
 let:znE aQ (Gl I) :=
   (zSO aQ (Gl I)).mpr
     (z12 aQ (Gl I)).injective
 have htower :=z5k (A:=Gl I) FX aQ
 rw [cua,htotal] at htower
 have hrel :zls aQ (Gl I)=1 := by
   apply Cardinal.eq_of_add_eq_add_left (a :=2)
   · exact htower.trans (by norm_num)
   · simp
 obtain ⟨e,he,hte⟩:=aSS aQ (Gl I)
 have he' : e=1 := by
   rw [hrel] at hte
   exact_mod_cast hte.symm
 simpa [he'] using he
end
end czb
end
section
namespace bzW
noncomputable section
open gT WJ MM Polynomial
open scoped nonZeroDivisors
attribute [local instance] Polynomial.algebra
variable {k A:Type} [zrb k] [za6 A] [zZE k A]
private theorem cA8 {S:Type} [za6 S] [zZE (e7 k) S]
   (f :S →+* zNv (A[X]))
   (hf : ∀ p:k[X],f (z12 (e7 k) S (z12 k[X] (e7 k) p)) =
     z12 A[X] (zNv (A[X])) (z12 k[X] A[X] p))
   {z :S} {p:A[X]} (hp:f z=z12 A[X] (zNv (A[X])) p)
   (hz :zxf (e7 k) z) :zxf k[X] p:= by
 obtain ⟨q,hq,hz⟩:=hz
 let j:=z12 A[X] (zNv (A[X]))
 let g:=f.comp (z12 (e7 k) S)
 have he :zmH g (f z) q=0:= by
   rw [← zly,← zCD,hz,zhc]
 have hcomp:g.comp (z12 k[X] (e7 k))=j.comp (z12 k[X] A[X]) :=
   zz4 hf
 refine ⟨IsLocalization.integerNormalization (k[X]⁰) q,
   mt IsFractionRing.integerNormalization_eq_zero_iff.mp hq,?_⟩
 have hh:=IsLocalization.integerNormalization_eval₂_eq_zero (k[X]⁰) g q he
 rw [hcomp,hp,← zly,← zCD] at hh
 exact (zxb A[X] (zNv (A[X]))) (hh.trans (zhc j).symm)
variable [ztn A]
private theorem b6m {p:A[X]} (hp:zxf k[X] p) :
  zsq k p.leadingCoeff := by
 obtain ⟨r,hr,hi⟩:=hp.exists_integral_multiple
 have hlead:=hi.coeff (r•p:A[X]).natDegree
 change zsq k (r•p:A[X]).leadingCoeff at hlead
 rw [zd5,leadingCoeff_mul,Polynomial.algebraMap_def,zKC,
  leadingCoeff_map_of_injective (z12 k A).injective] at hlead
 have hinv :=(z7i (R:=k) (A:=A) (x :=r.leadingCoeff⁻¹)).mul hlead
 rw [← ztg,← zok,inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hr),zXs,
  zkF] at hinv
 exact hinv
private theorem eoJ {x y :A}
  (h:zxf k[X] (C x+(z7y:A[X])*C y)) :zsq k x∧zsq k y := by
 have hy :zsq k y := by
  by_cases hy :y=0
  · simp [hy,isIntegral_zero]
  · have hl:=b6m h
    rwa [add_comm,zDE (z7y:A[X]),leadingCoeff_linear hy] at hl
 have hterm :zsq k[X] ((z7y:A[X])*C y) := by
  apply Polynomial.isIntegral_iff_isIntegral_coeff.mpr
  intro n
  rw [zDE,C_mul_X_eq_monomial,coeff_monomial]
  split_ifs
  · exact hy
  · exact isIntegral_zero
 have hx :zxf k[X] (C x :A[X]) := by
  simpa only [zY6] using h.sub hterm.isAlgebraic
 exact ⟨by simpa only [leadingCoeff_C] using b6m hx,hy⟩
private abbrev coord (D:znc (yT k)) (i:zNO (Fin 2)) :gk D :=
 zVv D (z9v i)
private theorem eFs (D:znc (yT k)) [D.IsPrime]
  (hdim:zqe (gk D)=1) :
  ¬ ∀ i,zsq k (coord D i) := by
 intro h
 let:zVK k (gk D) := by
  constructor
  intro a
  obtain ⟨p,rfl⟩:=zld a
  induction p using z5i with
  | C c=>exact isIntegral_algebraMap (x :=c)
  | add p q hp hq=>simpa only [map_add] using hp.add hq
  | mul_X p i hp=>simpa only [map_mul] using hp.mul (h i)
 have hfield :IsField (gk D) :=zJW (zB1 k)
 exact zero_ne_one ((z90 hfield).symm.trans hdim)
private theorem bwb (D:znc (yT k)) [ztn (Cz D)] :
    LX D =
      Je D (some 0)+algebraMap (e7 k) (CurveField D) (ajC k) *
        Je D (some 1) := by
  simp only [LX,Je,an9,Qe,zQb,
    z7N,RingHom.map_add,RingHom.map_mul]
  rw [zG3 (e7 k) (Cz D) (CurveField D)]
  rfl
set_option maxHeartbeats 800000 in
theorem proof :MM.c1 := by
  classical
  intro k _ D hD hdim
  let:D.IsPrime :=hD
  let A:=gk D
  let L:=zNv (A[X])
  obtain ⟨g,hg,hcoords,hscalar⟩:=gsF D
  let h:ztn (Cz D) :=Function.Injective.isDomain g hg
  refine ⟨h,?_⟩
  by_cases hs :zxf (e7 k) (LX D)
  · right
    intro hv
    let f :CurveField D →+* L:=zIj hg
    have hmap (a :Cz D) :f (z12 (Cz D) (CurveField D) a)=g a :=
      zoc hg a
    have hscalar' (p:k[X]) :f (z12 (e7 k) (CurveField D)
          (z12 k[X] (e7 k) p)) =
        aI2 A (p.map (z12 k A)) := by
      rw [zG3 (e7 k) (Cz D) (CurveField D),hmap]
      exact hscalar p
    have hcoord (i:zNO (Fin 2)) :
        f (Je D i)=aI2 A (C (coord D i)) := by
      change f (z12 (Cz D) (CurveField D)
        (auU D (z9v i)))= _
      rw [hmap,hcoords]
    have hp:f (LX D) =
        aI2 A (C (coord D (some 0)) +
          (z7y:A[X])*C (coord D (some 1))) := by
      rw [bwb D,f.map_add,f.map_mul,hcoord,hcoord,ajC,hscalar']
      simp only [zSo,RingHom.map_add,RingHom.map_mul]
    have hxy :=eoJ (cA8 (k :=k) (A:=A) f hscalar' hp hs)
    have hV:=b6m (cA8 (k :=k) (A:=A) f hscalar' (hcoord none) hv)
    simp only [leadingCoeff_C] at hV
    apply eFs D hdim
    intro i
    rcases i with _ | i
    · exact hV
    · fin_cases i
      · exact hxy.1
      · exact hxy.2
  · exact zMH hs
end
end bzW
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace cza
noncomputable section
open cu gT OH
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev aBZ:=z3y (Fin 4) aZ
def ar1 :z87 →+* aBZ:=zDK znf
def aI4 (i:Fin 2) :aBZ:=znf (z9v i)
def a6M:aBZ :=
 z9v 0+aI4 0*z9v 1-aI4 1
abbrev aoP (Q:znc z87) :znc aBZ :=
 Q.map ar1 ⊔ zye {a6M}
abbrev Ek :zdT aBZ :=
 (zgt aZ).map znf
private def avW (Q:znc z87) :z87 →+* zM1 (z87 ⧸ Q) :=
 Polynomial.C.comp (zVv Q)
def pD (Q:znc z87) :aZ →+* zM1 (z87 ⧸ Q) :=
  zOD ((avW Q).comp znf)
    ![z7y,avW Q (z9v 0) +
      z7y*avW Q (z9v 1)]
def aPo (Q:znc z87) :aBZ →+* zM1 (z87 ⧸ Q) :=
 zOD (pD Q) (fun i=>avW Q (z9v i))
private theorem c5c (Q:znc z87) :
  (aPo Q).comp ar1=avW Q:= by
 apply zXT <;> intro r <;>
  simp [aPo,ar1,pD]
private theorem eNB (Q:znc z87) :aoP Q≤zdq (aPo Q) := by
 apply zbX
 · rw [zo0,zEW,c5c]
   intro r hr
   simp [zry,avW,Ideal.Quotient.eq_zero_iff_mem.mpr hr]
 · rw [zvl,zry]
   simp [a6M,aI4,aPo,pD]
private def c50 (Q:znc z87) : (z87 ⧸ Q) →+* (aBZ ⧸ aoP Q) :=
 zP2 Q ((zVv (aoP Q)).comp ar1) fun _ hr =>
  Ideal.Quotient.eq_zero_iff_mem.mpr (zKg (z7X ar1 hr))
private def aPp (Q:znc z87) :
  zM1 (z87 ⧸ Q) →+* (aBZ ⧸ aoP Q) :=
 zqf (c50 Q) (zVv (aoP Q) (aI4 0))
private theorem c5b (Q:znc z87) :
  (aPp Q).comp (avW Q)=(zVv (aoP Q)).comp ar1 := by
 apply zz4
 intro r
 simp [aPp,avW,c50]
private theorem eNz (Q:znc z87) :
    (aPp Q).comp (pD Q) =
      (zVv (aoP Q)).comp MvPolynomial.C:= by
  let m:=zVv (aoP Q)
  have hline :m (z9v 0)+m (aI4 0)*m (z9v 1) =
      m (aI4 1) := by
    have h:m a6M=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
      (zs0 (z5J a6M))
    simpa [a6M,zpO,zrl,zok,zF3] using h
  have hconst (r :z87) :aPp Q (avW Q r)=m (ar1 r) :=
    zmU (c5b Q) r
  apply zXT
  · intro r
    simpa only [zQb,pD,zTv,ar1,
      zpw] using hconst (znf r)
  · intro i
    fin_cases i
    · simp [pD,aPp,aI4]
    · change aPp Q (pD Q (z9v 1))=m (aI4 1)
      rw [pD,zrD]
      change aPp Q (avW Q (z9v 0) +
        z7y*avW Q (z9v 1))=m (aI4 1)
      rw [zrl,zok,hconst,hconst]
      simpa [aPp,ar1,m] using hline
private theorem eNy (Q:znc z87) :
   (aPp Q).comp (aPo Q)=zVv (aoP Q) := by
 rw [aPo,MvPolynomial.comp_eval₂Hom,eNz]
 apply zXT
 · intro r
   simp
 · intro i
   have h:=zmU (c5b Q) (z9v i)
   simpa [ar1] using h
theorem c5d (Q:znc z87) :aoP Q=zdq (aPo Q) := by
 apply zWs (eNB Q)
 intro r hr
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 have h:=zmU (eNy Q) r
 simpa only [zQb,RingHom.mem_ker.mp hr,zhc] using h.symm
private theorem c5a : (z12 aBZ N8).comp ar1= Q6:= by
 rw [Q6,IsScalarTower.algebraMap_eq FX aZ aQ,zu8]
 exact zz4 (z6Y znf _)
theorem ccq (Q:znc z87) :
  (aoP Q).map (z12 aBZ N8)=Cr Q:= by
 have hline :z12 aBZ N8 a6M=B4 0 1 := by
  simp [a6M,aI4,B4,ek]
 simp only [aoP,zXe,z0L,c5a,zlN,
  zyl,hline]
private theorem eNA (Q:znc z87) : (aoP Q).comap ar1= Q:= by
 ext r
 rw [Ideal.mem_comap,c5d,zry]
 have h:=zmU (c5c Q) r
 change aPo Q (ar1 r)=avW Q r at h
 rw [h]
 simp [avW,z1Q]
theorem proof :OH.c5:= by
 intro Q hQ hproper
 let:Q.IsPrime :=hQ
 let:zNo Ek N8 :=
   zEY (zgt aZ) aQ
 have hprime : (aoP Q).IsPrime := by
   rw [c5d]
   exact zgL (aPo Q)
 have hdisjoint:=(z78
   Ek N8 (aoP Q)).mp ((ccq Q).trans_ne hproper)
 have hcontract :=ztT
   Ek N8 hprime hdisjoint
 constructor
 · rw [← ccq Q]
   exact znL Ek N8 _ hprime hdisjoint
 · rw [← ccq Q,← c5a,← zg6]
   exact (zPw (zK3 ar1) hcontract).trans (eNA Q)
end
end cza
end
section
namespace czo
noncomputable section
open axl
open IsLocalRing WithZero
open scoped Polynomial
variable {F:Type} [zrb F]
local notation "Dc" => aFI F
local notation "akv" => @RatFunc.inftyValuation F _ (Classical.decEq _)
private theorem bPF {x :ziC F} (hx :x≠0) :
  akv x=exp x.intDegree := by
 exact @RatFunc.inftyValuation_of_nonzero F _ (Classical.decEq _) x hx
private theorem b8W (a :Dc) :
  a∈zrY Dc↔akv (z12 Dc (ziC F) a)<1 :=
 zNC (ziC F) akv
private def parameter :Dc :=
 ⟨1/zyX,by
   change akv (1/zyX)≤1
   rw [zZm,z9J]
   omega⟩
private theorem djl (n:ℕ) :
  akv (z12 Dc (ziC F) ((parameter :Dc)^n))=exp (-(n:ℤ)) := by
 rw [zkq,zkq]
 change akv (1/zyX)^n= _
 rw [zZm,← zh5]
 congr 1
 simp
private theorem ezU :
   zrY Dc=zye ({parameter} : Set Dc) := by
 have ht:akv (z12 Dc (ziC F) (parameter :Dc))=exp (-1) := by
   simpa only [pow_one,Nat.cast_one] using djl (F:=F) 1
 ext a
 rw [b8W,zxV,
   (z9W akv).dvd_iff_le,ht]
 by_cases ha :z12 Dc (ziC F) a=0
 · simp [ha]
 · rw [bPF ha,zqL,zSP]
   omega
private theorem eOv (a :Dc) (ha :a≠0) :
   ∃ n:ℕ,(n:ℤ) = -(z12 Dc (ziC F) a).intDegree ∧
     zye ({a} : Set Dc)=zrY Dc^n:= by
 let x :=z12 Dc (ziC F) a
 have hv :=z9W akv
 have hx :x≠0:=(zw1 _ hv.hom_inj).mpr ha
 have hval :akv x=exp x.intDegree :=bPF hx
 have hle :akv x≤1 :=a.property
 rw [hval,z9J] at hle
 let n:=(-x.intDegree).toNat
 have hn: (n:ℤ) = -x.intDegree :=Int.toNat_of_nonneg (neg_nonneg.mpr hle)
 refine ⟨n,hn,?_⟩
 rw [ezU,zNi,le_antisymm_iff,
   zou,zou]
 rw [hv.dvd_iff_le,hv.dvd_iff_le,
   djl,hn,neg_neg]
 change (akv x≤exp x.intDegree)∧(exp x.intDegree≤akv x)
 simp [hval]
private theorem gKU {x :ziC F} (hx :x≠0)
   (hd:x.intDegree=0) :
   akv (x - ztW x.num.leadingCoeff)<1 := by
 let c:=x.num.leadingCoeff
 let p:=x.num-Polynomial.C c*x.denom
 let m:=z12 F[X] (ziC F)
 have hcn:c≠0:=Polynomial.leadingCoeff_ne_zero.mpr (zl3 hx)
 have hq:m x.denom≠0:= by
   exact (zw1 _ (zxb F[X] (ziC F))).mpr x.denom_ne_zero
 have hsub:x - ztW c=m p/m x.denom:= by
   change x - ztW c=m (x.num-Polynomial.C c*x.denom)/m x.denom
   rw [zpO,zok]
   change x - ztW c=(m x.num - m (z1z c)*m x.denom)/m x.denom
   simp only [m,zyJ]
   rw [← div_sub_div_same,mul_div_cancel_right₀ _ hq,RatFunc.num_div_denom]
 change akv (x - ztW c)<1
 rw [hsub]
 by_cases hp:p=0
 · simp [hp]
 have hnp:m p≠0 :=
   (zw1 _ (zxb F[X] (ziC F))).mpr hp
 have hdegrees :x.num.natDegree=x.denom.natDegree := by
   unfold zfy at hd
   omega
 have hscaled:z1z c*x.denom≠0 :=
   zBS (Polynomial.C_ne_zero.mpr hcn) x.denom_ne_zero
 have hdegEq:x.num.degree=(z1z c*x.denom).degree := by
   rw [zPS (zl3 hx),
     zPS hscaled,Polynomial.natDegree_C_mul hcn,hdegrees]
 have hdeg:p.degree<x.num.degree :=
   Polynomial.degree_sub_lt_left hdegEq (zl3 hx)
     ((RatFunc.monic_denom x).leadingCoeff_C_mul c).symm
 have hlt:p.natDegree<x.denom.natDegree :=
   hdegrees ▸ Polynomial.natDegree_lt_natDegree hp hdeg
 rw [bPF (div_ne_zero hnp hq),zqL,
   RatFunc.intDegree_div hnp hq]
 change (z12 F[X] (ziC F) p).intDegree -
   (z12 F[X] (ziC F) x.denom).intDegree<0
 rw [ztb,ztb]
 omega
private theorem fWY :
   zpX (z12 F (zhZ Dc)) := by
 intro z
 obtain ⟨a,rfl⟩:=z6A (R:=Dc) z
 change ∃ c:F,residue Dc (z12 F Dc c)=residue Dc a
 have hle :akv (z12 Dc (ziC F) a)≤1 :=a.property
 rcases hle.lt_or_eq with hlt | heq
 · refine ⟨0,?_⟩
   rw [zhc,zhc,eq_comm,residue_eq_zero_iff,b8W]
   exact hlt
 · let x :=z12 Dc (ziC F) a
   have hx :x≠0:= by
    intro h
    have hv :akv x=1 :=heq
    simp [h] at hv
   have hd:x.intDegree=0:= by
    have h:exp x.intDegree=1 :=(bPF hx).symm.trans heq
    exact WithZero.exp_injective (h.trans (zva (M:=ℤ)).symm)
   refine ⟨x.num.leadingCoeff,?_⟩
   apply Eq.symm
   rw [← zF3,← zpO,residue_eq_zero_iff,b8W]
   rw [zpO,← zG3 F Dc (ziC F),z4W]
   exact gKU hx hd
private theorem yC (a :Dc) (ha :a≠0) :
    zAa F (Dc ⧸ zye {a}) ∧
      (zsE F (Dc ⧸ zye {a}) :ℤ) =
        -(z12 Dc (ziC F) a).intDegree := by
  let _:=cU9 F
  let _:IsLocalHom (z12 F Dc) :=⟨fun c hc=>isUnit_iff_ne_zero.mpr
    (fun h=>hc.ne_zero (by rw [h,zhc]))⟩
  have hsurj:zpX (z12 (zhZ F) (zhZ Dc)) := by
    intro z
    obtain ⟨c,rfl⟩:=fWY z
    exact ⟨residue F c,ResidueField.algebraMap_residue c⟩
  have hres :zKQ (zhZ F) (zhZ Dc)=1 :=
    (zAi (M:=zhZ Dc) hsurj).trans (Module.length_eq_one _ _)
  obtain ⟨n,hn,hI⟩:=eOv a ha
  let Q:=Dc ⧸ zye ({a} : Set Dc)
  have hO:zKQ Dc Q=n:= by
    change zKQ Dc (Dc ⧸ zye ({a} : Set Dc))=n
    rw [hI,zRe]
  have hF:zKQ F Q=n:= by
    rw [z9y F Dc Q,hO,hres,zqg]
  have hfinlen:IsFiniteLength F Q:=Module.length_ne_top_iff.mp (by rw [hF]; simp)
  let _:IsNoetherian F Q:=(isFiniteLength_iff_isNoetherian_isArtinian.mp hfinlen).1
  have hrank :=zPw ENat.toNat ((z1C F Q).symm.trans hF)
  refine ⟨zWv,?_⟩
  change (zsE F Q:ℤ)= _
  have hrank' : zsE F Q=n:= by simpa only [zzq] using hrank
  exact (zPw (fun k :ℕ=>(k :ℤ)) hrank').trans hn
theorem proof :axl.c2 :=
 fun _ _ a ha=>yC a ha
end
end czo
end
section
set_option backward.isDefEq.respectTransparency false
namespace czn
noncomputable section
open MM axl
open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid
open scoped Classical
variable {F B K:Type} [zrb F] [za6 B] [zJZ B] [zrb K]
 [zZE F B] [zZE F K] [zZE B K] [zsf F B K] [z0o B K]
private theorem auz (p:zZx B) {a :B} (ha :a≠0) :
  KB (aMP p:zZ F K) (z12 B K a) =
   zug p.asIdeal (zye {a}) := by
 change (-WithZero.log (p.valuation K (z12 B K a))).toNat= _
 simp only [p.valuation_of_algebraMap,p.intValuation_eq_exp_neg_multiplicity ha,
  zOL,neg_neg,zQf]
private theorem eOf (p:zZx B) (n:ℕ) :
    zsE F (B ⧸ p.asIdeal^n) =
      QZ (aMP p:zZ F K)*n:= by
  let w:zZ F K:=aMP p
  let V:=w.val.valuationSubring
  let:zZE B V:=((z12 B K).codRestrict V.toSubring
    (p.valuation_le_one (K:=K))).toAlgebra
  let:zsf F B V:=zsL fun c=> by
    apply zkt
    exact zG3 F B K c
  let e :p.valuationSubringAtPrime K ≃ₐ[B] V :=
    { zh4 (zPw zJ2
        (p.valuationSubringAtPrime_eq_valuationSubring (K:=K))) with
      commutes' := fun _=>zkt rfl }
  let:zNo p.asIdeal.primeCompl V :=
    zfY p.asIdeal.primeCompl e
  let:z8E V :=
    zx9 B p.ne_bot V
  let q:=(zYv p.asIdeal V n).restrictScalars F
  have hres : (zKQ (zhZ F) (zhZ V)).toNat =
      zsE F (zhZ V) := by
    rw [← zAi (R:=zhZ F)
      (z6A (R:=F)),zqA,zPK]
    rfl
  have hlen:=z9y F V (V ⧸ zrY V^n)
  rw [zRe] at hlen
  have hd:=zPw ENat.toNat hlen
  simp only [ENat.toNat_mul,zzq] at hd
  rw [hres,zqA,zPK] at hd
  change zsE F (B ⧸ p.asIdeal^n)=zsE F (zhZ V)*n
  rw [q.toLinearEquiv.finrank_eq,zDE]
  exact hd
private abbrev apX (I:znc B) :=(factors I).toFinset
private def aUx {I:znc B} (p:apX I) :zZx B :=
 HeightOneSpectrum.ofPrime (prime_of_factor p.val (Multiset.mem_toFinset.mp p.property))
theorem proof :axl.c1 := by
  classical
  intro F B K _ _ _ _ _ _ _ _ _ a ha hfin
  let I:znc B:=zye {a}
  have hI:I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
  let n (p:apX I) :=(factors I).count p.val
  let e :=zsT hI
  let eF: (B ⧸ I) ≃ₐ[F] ∀ p:apX I,B ⧸ p.val^n p :=
    { e with
      commutes' := fun c=> by
        funext p
        change e (zVv _ (z12 F B c)) p =
          zVv _ (z12 F B c)
        rw [znh] }
  let primes :apX I ↪ zZx B :=
    ⟨aUx,fun _ _ h=>zkt (zPw HeightOneSpectrum.asIdeal h)⟩
  have support (p:zZx B) :p.asIdeal∈(factors I).toFinset↔a∈p.asIdeal:= by
    rw [Multiset.mem_toFinset,zy7,Ideal.mem_normalizedFactors_iff hI]
    exact (and_iff_right p.isPrime).trans (zvl p.asIdeal)
  refine ⟨Finset.univ.map primes,?_,?_⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨q,_,rfl⟩:=Finset.mem_map.mp hp
      exact (support (primes q)).mp q.property
    · intro hp
      let q:apX I:=⟨p.asIdeal,(support p).mpr hp⟩
      exact Finset.mem_map.mpr ⟨q,Finset.mem_univ q,HeightOneSpectrum.ext rfl⟩
  · let:zAa F (B ⧸ I) :=hfin
    let:zAa F (∀ p:apX I,B ⧸ p.val^n p) :=
      zZc eF.toLinearEquiv
    have (p:apX I) :zAa F (B ⧸ p.val^n p) := by
      let proj: (∀ q:apX I,B ⧸ q.val^n q) →ₗ[F] B ⧸ p.val^n p :=
        LinearMap.proj p
      exact zIU proj (LinearMap.proj_surjective p)
    change zsE F (B ⧸ I)= _
    rw [eF.toLinearEquiv.finrank_eq,z0r,z93]
    apply zUo rfl
    intro p _
    have hn:KB (aMP (primes p) :zZ F K) (z12 B K a)=n p:= by
      rw [auz _ ha]
      change zug (primes p).asIdeal I=(factors I).count (primes p).asIdeal
      rw [zy7,zwP hI]
    rw [hn]
    exact eOf (F:=F) (K:=K) (primes p) (n p)
end
end czn
end
section
namespace cy9
open OH Polynomial
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin nonZeroDivisors
noncomputable section
variable {k A:Type} [zrb k] [za6 A] [ztn A] [zZE k A]
private theorem bx2 [zUK k A] (hdim:zqe A=1) :
   zls k (zNv A)≤1 := by
 obtain ⟨n,g,hg,hint⟩:=zGH k A
 let P:=z3y (Fin n) k
 let F:=zNv A
 let:zZE P A:=g.toRingHom.toAlgebra
 have :zVK P A:=⟨hint⟩
 have hnP: (n:zUi ℕ∞)≤ zqe P:= by
   simpa only [P,zZT,zOP,zJa] using
     (zbi (R:=k) (Fin n))
 obtain ⟨l,hl⟩:=Order.le_krullDim_iff.mp hnP
 have hker :zdq (z12 P A) = ⊥ :=
   (zli _).mp hg
 obtain ⟨J,hJ,hover⟩:=Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
   (S:=A) l.head.asIdeal (by rw [hker]; exact bot_le)
 let:J.IsPrime :=hJ
 let:J.LiesOver l.head.asIdeal:=⟨hover.symm⟩
 obtain ⟨L,hL,_,_⟩:=z1m l J
 have hlen: (n:zUi ℕ∞)≤1 := by
   rw [← hl,← hL,← hdim]
   exact Order.LTSeries.length_le_krullDim L
 have hn:n≤1 := by exact_mod_cast hlen
 have :zsf k P F:=zsL fun c=> by
   rw [zG3 P A F,zG3 k A F]
   exact zPw (z12 A F) (g.commutes c).symm
 have :znE P A:=(zSO P A).mpr hg
 have :zjH A F:=zyQ F A⁰
 have :zjH P F:=z1q P A F
 have hb:=(z8S (Fin n) k).algebraMap_comp (A:=F)
 have htr :zls k F=(n:zpf) := by
   simpa using hb.cardinalMk_eq_trdeg.symm
 rw [htr]
 exact_mod_cast hn
private theorem eaV [zUK k A] (hdim:zqe A=1)
  {x :zNv A} (hx :znN k x) :
  zAa (zvb k ({x} : Set (zNv A))) (zNv A) := by
 let F:=zNv A
 let E :=zvb k ({x} : Set F)
 have hx_ind:AlgebraicIndependent k (fun _:Unit=>x) :=
  (algebraicIndependent_singleton_iff ()).2 hx
 have hx_basis :=hx_ind.isTranscendenceBasis_of_trdeg_le_of_finite
  (by simpa using bx2 (k :=k) hdim)
 have hx_range :zxp (fun _:Unit=>x) = {x} := Set.range_const
 have :zjH E F:=Eq.mp
  (zPw (fun s=>zjH (zvb k s) F) hx_range)
  hx_basis.isAlgebraic_field
 have :zl5 A F :=
  zrU F A⁰
 have :zl5 k F:=zQi k A F
 have :zl5 E F:=z9q k E F
 exact zNf
private theorem cci {f :A} {ι:Type} {v :ι→A} (hf :f≠0)
  (hv :z14 k (fun i=>zVv (zye {f}) (v i)))
  (s :zJe ι) (p:ι→zM1 k)
  (h : ∑ i∈s,zEU f (p i)*v i=0) :
  ∀ i∈s,p i=0:= by
 classical
 intro i hi
 by_contra hpi
 have hex : ∃ d:ℕ,∃ j∈s,(p j).coeff d≠0 :=
  ⟨(p i).natTrailingDegree,i,hi,coeff_natTrailingDegree_ne_zero.mpr hpi⟩
 let m:=zqr hex
 obtain ⟨j,hj,hcoeff⟩:=zWq hex
 have hd : ∀ l∈s,(z7y:zM1 k)^m∣p l:= by
  intro l hl
  apply X_pow_dvd_iff.mpr
  intro d hd
  by_contra hne
  exact Nat.find_min hex hd ⟨l,hl,hne⟩
 choose! q hq using hd
 have hmul :f^m*(∑ l∈s,zEU f (q l)*v l)=0:= by
  rw [← h,zxw]
  apply zUo rfl
  intro l hl
  simp [hq l hl,ztg]
 have hqsum:=(mul_eq_zero.mp hmul).resolve_left (zm1 _ hf)
 let π:=zvR k (zye ({f} : Set A))
 have hπf :π f=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (z5J f)
 have hred:=zPw π hqsum
 simp only [zdo,zok,zhc,← zTM,hπf,
  ← coeff_zero_eq_aeval_zero',← zd5] at hred
 have hzero : (q j).coeff 0=0:=(linearIndependent_iff'.mp hv) s _ hred j hj
 apply hcoeff
 change (p j).coeff m=0
 rw [hq j hj,coeff_X_pow_mul',zYp zs1,Nat.sub_self,hzero]
set_option backward.isDefEq.respectTransparency false in
private theorem en4 {f :A} {ι:Type} {v :ι→A} (hf :f≠0)
   (hv :z14 k (fun i=>zVv (zye {f}) (v i))) :
   z14 (zvb k {z12 A (zNv A) f})
     (fun i=>z12 A (zNv A) (v i)) := by
 let F:=zNv A
 let x :F:=z12 A F f
 let B:=zum k ({x} : Set F)
 let E :=zvb k ({x} : Set F)
 apply (LinearIndependent.iff_fractionRing B E).mp
 rw [linearIndependent_iff']
 intro s c hc i hi
 have hcoef (j:ι) : ∃ p:zM1 k,zEU x p=(c j:F) :=
   zOc k x (c j)
 choose p hp using hcoef
 let embed:=zE2 k A F
 have h : ∑ j∈s,zEU f (p j)*v j=0:= by
   apply (zxb A F)
   change embed (∑ j∈s,zEU f (p j)*v j)=embed 0
   simp only [zdo,zok,zhc,← zTM]
   change (∑ j∈s,zEU x (p j)*z12 A F (v j))=0
   simp only [zd5] at hc
   change (∑ j∈s,(c j:F)*z12 A F (v j))=0 at hc
   simpa only [hp] using hc
 apply zkt
 change (c i:F)=0
 rw [← hp i,cci hf hv s p h i hi,zhc]
theorem proof :OH.c4 := by
 classical
 intro k A _ _ _ _ _ hdim f hf
 let F:=zNv A
 let x :F:=z12 A F f
 let Q:=PrincipalCut f
 by_cases hx :znN k x
 · let E :=zvb k ({x} : Set F)
   have :zAa E F:=eaV hdim hx
   let b:=Module.Basis.ofVectorSpace k Q
   choose v hv using fun i=>zld (b i)
   have hli:z14 k (fun i=>zVv (zye {f}) (v i)) := by
     simpa only [hv] using b.linearIndependent
   have hLift:z14 E (fun i=>z12 A F (v i)) :=en4 hf hli
   let:Finite (z3h k Q) :=hLift.finite
   let:Fintype (z3h k Q) :=Fintype.ofFinite _
   change zsE k Q≤FZ k F x
   rw [Module.finrank_eq_card_basis b,FZ,zYp hx]
   exact hLift.fintype_card_le_finrank
 · have hfa :zxf k f :=(isAlgebraic_algebraMap_iff (R:=k)
     (zxb A F)).mp (not_not.mp hx)
   have hu:zWB f :=IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor
     hfa.isIntegral (mem_nonZeroDivisors_of_ne_zero hf)
   have :zOt Q :=
     Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
   change zsE k Q≤aHf k A f
   rw [zuF]
   exact zD0 _
end
end cy9
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace baA
noncomputable section
open cu gT pI MvPolynomial
open scoped Polynomial RatFunc nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
private abbrev aLZ:=z3y Unit aZ
private abbrev aF4 :=z3y Unit aQ
private abbrev aKJ:=ziC aQ
private abbrev Parameters :=z3y (Fin 4) FX
private def aD9:Unit ⊕ Fin 2→Fin 4 :=
 Sum.elim (fun _=>3) ![0,2]
private theorem eJU:zq4 aD9:= by decide
private def a6o:aLZ →+* Parameters :=
 (zHw aD9).toRingHom.comp (zm2 FX Unit (Fin 2)).symm.toRingHom
private theorem eJX:zq4 a6o :=
 (zLm _ eJU).comp (zm2 FX Unit (Fin 2)).symm.injective
private local instance gQx :zZE aF4 aKJ :=
 zYo _ (zpe aQ Unit).toRingEquiv.toRingHom
private local instance gQw:z0o aF4 aKJ :=
 zwJ (zpe aQ Unit).toRingEquiv fun _=>rfl
private abbrev Ek :zdT aLZ:=aZ⁰.map znf
private local instance :zNo Ek aF4 :=
 zEY aZ⁰ aQ
private def bts :aLZ →+* dV :=
 (z12 Parameters dV).comp a6o
private theorem c3A:zq4 bts := by
 change zq4 (fun p=>z12 Parameters dV (a6o p))
 exact (zxb Parameters dV).comp eJX
private theorem cbm (y :Ek) :zWB (bts y) := by
 obtain ⟨c,hc,he⟩:=y.property
 refine isUnit_iff_ne_zero.mpr fun hz => ?_
 have hzero : (y :aLZ)=0 :=
  c3A (hz.trans (zhc bts).symm)
 exact (zw1 znf (zbo Unit aZ)).mpr
  (mem_nonZeroDivisors_iff_ne_zero.mp hc) (he.trans hzero)
private def azx :aF4 →+* dV :=
 zvq (M:=Ek) (g:=bts) cbm
private theorem cYH :zq4 azx := by
 apply (zcf (S:=aF4) cbm).mpr
 intro p q
 have hi:zq4 (z12 aLZ aF4) :=
  zNV _ (zxb aZ aQ)
 rw [hi.eq_iff,c3A.eq_iff]
private abbrev b6q (p:aLZ) :aKJ :=
 z12 aF4 aKJ (z12 aLZ aF4 p)
private theorem dcR (p:aZ) :
  b6q (C p)=ztW (z12 aZ aQ p) := by
 change z12 (zM1 aQ) aKJ
  (zpe aQ Unit (zDK (z12 aZ aQ) (C p)))= _
 simp [zJG,zyJ]
private theorem gop:b6q (z9v ())=RatFunc.X:= by
 change z12 (zM1 aQ) aKJ
  (zpe aQ Unit (zDK (z12 aZ aQ) (z9v ())))= _
 simp [zJG,zYR]
def bf0:aKJ →+* dV :=
  zIj (K:=aKJ)
    (g:=azx) cYH
private theorem caJ (p:aLZ) :
   bf0 (b6q p)=z12 Parameters dV (a6o p) := by
 change zIj cYH
   (z12 aF4 aKJ (z12 aLZ aF4 p)) =
     bts p
 rw [zoc]
 exact zX4 cbm p
def IL:aQ →+* dV :=
 bf0.comp ztW
theorem coW (c:FX) :
  IL (z12 FX aQ c)=z12 FX dV c:= by
 change bf0 (ztW (z12 aZ aQ (C c))) =
  z12 Parameters dV (C c)
 rw [← dcR,caJ]
 simp [a6o]
theorem dcE (i:Fin 2) :
  IL (ek i)=kz (![0,2] i) := by
 change bf0 (ztW (z12 aZ aQ (z9v i)))= _
 rw [← dcR,caJ]
 simp [a6o,aD9,kz]
theorem eHO:bf0 zyX=kz 3:= by
 rw [← gop,caJ]
 simp [a6o,aD9,kz]
end
end baA
end
section
set_option maxHeartbeats 1200000
namespace baA
noncomputable section
open scoped Polynomial TensorProduct
open Algebra.TensorProduct
variable {k F σ:Type} [zrb k] [zrb F] [zZE k F]
abbrev ke (J:znc (z3y σ k)) (j:σ) (u:F) :
  znc (z3y σ F) :=
 J.map (zDK (z12 k F)) ⊔ zye {z9v j-MvPolynomial.C u}
def bp4 {P A:Type} [za6 P] [za6 A] [zZE k P]
    [zZE k A] [zZE P A] [zZE P F] [zsf k P A] [zsf k P F]
    (J:znc (z3y σ k)) (e : (z3y σ k ⧸ J) ≃ₐ[k] A)
    (j:σ) (t:P) (u:F)
    (hext : ∀ {B:Type} [za6 B] [zZE k B] {f g:P →ₐ[k] B},f t=g t→f=g)
    (hq:z12 P A t=e (zVv J (z9v j)))
    (hu:z12 P F t=u) :
    F ⊗[P] A ≃ₐ[F] (z3y σ F ⧸ ke J j u) := by
  let q:z3y σ k →ₐ[k] A:=e.toAlgHom.comp (zvR k J)
  let T:=F ⊗[P] A
  let S:=z3y σ F ⧸ ke J j u
  let:zsf k F T:=zWv
  let:zsf k F S:=zWv
  letI algebraPS:zZE P S:=zYo S (z12 P F)
  let:SMul P S:=algebraPS.toSMul
  let:zsf P F S:=zD8 (R:=P) (S:=F) (A:=S) rfl
  let:zsf k P T:=IsScalarTower.to₁₂₄ k P F T
  let right:A →ₐ[P] T:=zgi
  let rightk :A →ₐ[k] T:=right.restrictScalars k
  let m:z3y σ F →ₐ[F] S:=zvR F _
  let ext:z3y σ k →ₐ[k] z3y σ F :=
    MvPolynomial.mapAlgHom (zNX k F)
  let eval :z3y σ F →ₐ[F] T :=
    zIe fun i=>right (q (z9v i))
  have heval : (eval.restrictScalars k).comp ext=rightk.comp q:= by
    apply zpH
    intro i
    simp [eval,ext,rightk]
  have hxt:right (q (z9v j))=z12 F T u:= by
    change right (e (zVv J (z9v j)))= _
    rw [← hq,right.commutes,zG3 P F T,hu]
  have hkill:ke J j u≤zdq eval.toRingHom:= by
    apply zbX
    · rw [zo0]
      intro p hp
      change eval (ext p)=0
      have h:=zcI heval p
      change eval (ext p)=right (q p) at h
      have hp₀:zVv J p=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hp
      rw [h,show q p=e (zVv J p) from rfl,hp₀,zhc,zhc]
    · rw [Ideal.span_le]
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      change eval (z9v j-MvPolynomial.C u)=0
      rw [zpO,zF3,zTw,zXr]
      exact hxt
  let forward:S →ₐ[F] T:=zTA _ eval fun p hp=>hkill hp
  let qext:z3y σ k →ₐ[k] S:=(m.restrictScalars k).comp ext
  let fromQuotient:=zTA J qext fun p hp=> by
    have hle :J.map (zDK (z12 k F))≤ke J j u:=le_sup_left
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (z7X _ hp))
  let fromA:A →ₐ[k] S:=fromQuotient.comp e.symm.toAlgHom
  have hfromA (p:z3y σ k) :fromA (q p)=qext p:= by
    change fromQuotient (e.symm (e (zVv J p)))=qext p
    rw [e.symm_apply_apply]
    rfl
  have hxs :fromA (q (z9v j))=z12 F S u:= by
    rw [hfromA]
    change m (ext (z9v j))=m (znf u)
    rw [show ext (MvPolynomial.X j)=MvPolynomial.X j by simp [ext],
      ← zF3,← zpO]
    have hle :zye {z9v j-MvPolynomial.C u} ≤ ke J j u:=le_sup_right
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (zCn (by simp)))
  let fromAP:A →ₐ[P] S :=
    { fromA.toRingHom with
      commutes' := by
        have h:fromA.comp (zE2 k P A) =
            (zE2 k F S).comp (zE2 k P F) := by
          apply hext
          change fromA (z12 P A t)=z12 F S (z12 P F t)
          rw [hq,hu]
          exact hxs
        exact zcI h }
  let backward:T →ₐ[F] S:=AlgHom.liftEquiv P F A S fromAP
  have hbackward (a :A) :backward (right a)=fromA a := by
    change backward (1 ⊗ₜ[P] a)=fromA a
    exact (AlgHom.liftEquiv_tmul (R:=P) fromAP (1 :F) a).trans (one_smul F _)
  have hforward (p:z3y σ k) :forward (qext p)=right (q p) :=
    zcI heval p
  have hST: (forward.comp backward:T →ₐ[F] T)=zhD F T:= by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    have hqsurj:zpX q:=e.surjective.comp zld
    rintro a
    obtain ⟨p,rfl⟩:=hqsurj a
    change forward (backward (right (q p)))=right (q p)
    rw [hbackward,hfromA]
    exact hforward p
  have hTS: (backward.comp forward:S →ₐ[F] S)=zhD F S:= by
    apply Ideal.Quotient.algHom_ext
    apply zpH
    intro i
    change backward (forward (m (z9v i)))=m (z9v i)
    rw [show m (MvPolynomial.X i)=qext (MvPolynomial.X i) by simp [qext,ext],
      hforward,hbackward,hfromA]
  exact (AlgEquiv.ofAlgHom forward backward hST hTS).symm
end
end baA
end
section
set_option backward.isDefEq.respectTransparency false
namespace baC
theorem proof :MM.c6:= by
 intro F A _ _ _ _ _ hfinite hdedekind a ha
 let K:=zNv A
 let B:=zwB A K
 let:zAa A B:=hfinite
 let:zJZ B:=hdedekind
 let:zUK F B:=Algebra.FiniteType.trans ‹Algebra.FiniteType F A› zWv
 let:z0o B K:=integralClosure.isFractionRing_of_finite_extension K K
 obtain ⟨hf,heq⟩:=dOp (F:=F) a ha
 have hb:z12 A B a≠0:= by
  intro h
  have hK:z12 A K a=0:=zPw Subtype.val h
  exact ha (zxb A K (hK.trans (zhc _).symm))
 obtain ⟨S,hS⟩:=eFq (F:=F) (K:=K) (z12 A B a) hb
 rw [← zG3 A B K] at hS
 exact ⟨hf,S,(heq.trans hS).le⟩
end baC
end
section
set_option maxHeartbeats 1200000
namespace baA
noncomputable section
open cu gT pI OH aiM
open scoped Polynomial TensorProduct
attribute [local instance] Polynomial.algebra
private theorem aHV (I:znc z87) :
    let:zZE aQ dV:=IL.toAlgebra
    ke (Cr I) 2 (kz 3) =
      I.map AU ⊔
        zye {JN,z9v 2 - znf (kz 3)} := by
  let:zZE aQ dV:=IL.toAlgebra
  change (Cr I).map (zDK IL) ⊔ _ = _
  have hbase : (zDK IL).comp Q6=AU:= by
    apply zXT
    · intro c
      simp [Q6,AU,coW]
    · intro j
      simp [Q6,AU]
  have hline :zDK IL (B4 (n:=4) 0 1)=JN := by
    have h₀:IL (ek 0)=kz 0:=dcE 0
    have h₁:IL (ek 1)=kz 2 :=dcE 1
    simp [B4,JN,h₀,h₁]
  rw [Cr,zXe,z0L,hbase,zlN,zyl,
    hline,sup_assoc,← zf9]
private theorem d98 {k F A σ:Type} [zrb k] [zrb F] [za6 A]
    [zZE k A] [zZE k F] [zZE (ziC k) F]
    (J:znc (z3y σ k)) (q: (z3y σ k ⧸ J) ≃ₐ[k] A) (j:σ) (u:F)
    (hC : ∀ c:k,z12 k F c=z12 (ziC k) F (ztW c))
    (hX:z12 (ziC k) F zyX=u) :
    zsE (ziC (ziC k))
        (anE (ziC k) (Gd k A (q (zVv J (z9v j))))) =
      zsE F (z3y σ F ⧸ ke J j u) := by
  let P:=zM1 k
  let U:=ziC k
  let x :=q (zVv J (z9v j))
  let:zZE P A:=(zEU x :P →ₐ[k] A).toRingHom.toAlgebra
  let:zZE P F:=zYo F (z12 P U)
  let:SMul P A:=(zWv :zZE P A).toSMul
  let:SMul P F:=(zWv :zZE P F).toSMul
  let:zsf P U F :=
    zD8 (R:=P) (S:=U) (A:=F) rfl
  let:zsf k P A:=zsL (R:=k) (S:=P) (A:=A)
    fun c=>(z8q x c).symm
  let:zsf k P F:=zsL (R:=k) (S:=P) (A:=F) <| by
    intro c
    change z12 k F c=z12 U F (z12 P U (z1z c))
    rw [zyJ,hC]
  have hparam:z12 P F z7y=u:= by
    change z12 U F (z12 P U z7y)=u
    rw [zYR,hX]
  let G:=Gd k A x
  let e :F ⊗[U] G ≃ₐ[F] F ⊗[P] A :=
    Algebra.TensorProduct.cancelBaseChange P U F F A
  let f :F ⊗[P] A ≃ₐ[F] (z3y σ F ⧸ ke J j u) :=
    bp4 J q j (z7y:P) u
      (fun h=>Polynomial.algHom_ext h) (zw0 x) hparam
  change zsE (ziC U) (anE U G) =
    zsE F (z3y σ F ⧸ ke J j u)
  calc
    _=zsE U G:=zXY
    _=zsE F (F ⊗[U] G) :=Module.finrank_baseChange.symm
    _=zsE F (z3y σ F ⧸ ke J j u) :=
      (e.trans f).toLinearEquiv.finrank_eq
theorem proof :aiM.c2 := by
 intro I
 let:zZE aQ dV:=IL.toAlgebra
 let:zZE (ziC aQ) dV:=bf0.toAlgebra
 have h:=d98 (F:=dV) (Cr I) (AlgEquiv.refl (R:=aQ) (A₁:=rM I))
  2 (kz 3) (fun _=>rfl) eHO
 exact h.trans (z9k dV (aHV I)).toLinearEquiv.finrank_eq
end
end baA
end
section
namespace ac2
noncomputable section
open cu gT
def Jl:z87 ≃+* z3y (Fin 2) aZ :=
  ((zGY FX (ziU (m:=2) (n:=2)).symm).trans
    (z3k FX (Fin 2) (Fin 2))).toRingEquiv
def qO:aZ →+* Ambient :=
 (zHw (zzs 2 :Fin 2→Fin 4)).toRingHom
def Ih {A:Type*} [za6 A] (a :aZ →+* A) :
    z87 →+* z3y (Fin 2) A :=
  (zDK a).comp Jl.toRingHom
abbrev agI (I:znc z87) :=gk (I.comap qO)
abbrev Tw (I:znc z87) :=zNv (agI I)
def avd (I:znc z87) :aZ →+* Tw I :=
  (z12 (agI I) (Tw I)).comp
    (zVv (I.comap qO))
def T3 (I:znc z87) :
    z87 →+* z3y (Fin 2) (Tw I) :=
  Ih (avd I)
def aml {A:Type*} [za6 A] (f :z3y (Fin 2) A) :
    List (Fin 2)→z3y (Fin 2) A
  | []=>f
  | i :: t=>MvPolynomial.pderiv i (aml f t)
def bp3 {A:Type*} [za6 A] (J:znc (z3y (Fin 2) A))
    (f :z3y (Fin 2) A) (r :ℕ) :Prop :=
  ∀ t:List (Fin 2),t.length≤ r→aml f t∈J
end
end ac2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ac2
noncomputable section
open cu gT pI Polynomial

@[simp] theorem gRL (c:FX) :
   Jl (znf c)=znf (znf c) := by
  simp [Jl]
@[simp] theorem gor (i:Fin 2) :
    Jl (z9v (zVs 2 i))=z9v i:= by
  change z3k FX (Fin 2) (Fin 2)
    (zGY FX (ziU (m:=2) (n:=2)).symm
      (z9v (zVs 2 i)))= _
  rw [zyk,z6l,
    finSumFinEquiv_symm_apply_castAdd,zwY]
@[simp] theorem bNE (i:Fin 2) :
    Jl (z9v (zzs 2 i))=znf (z9v i) := by
  change z3k FX (Fin 2) (Fin 2)
    (zGY FX (ziU (m:=2) (n:=2)).symm
      (z9v (zzs 2 i)))= _
  rw [zyk,z6l,
    finSumFinEquiv_symm_apply_natAdd,zoo]
@[simp] theorem bOe {A:Type*} [za6 A] (a :aZ →+* A) (c:FX) :
   Ih a (znf c)=znf (a (znf c)) := by
  simp [Ih]
@[simp] theorem bOg {A:Type*} [za6 A] (a :aZ →+* A) (i:Fin 2) :
   Ih a (z9v (zVs 2 i))=z9v i:= by
  change zDK a (Jl (z9v (zVs 2 i)))= _
  rw [gor,z7N]
@[simp] theorem bwR {A:Type*} [za6 A] (a :aZ →+* A) (i:Fin 2) :
   Ih a (z9v (zzs 2 i))=znf (a (z9v i)) := by
  change zDK a (Jl (z9v (zzs 2 i)))= _
  rw [bNE,zpw]
theorem aVL:CG=Ih (z12 aZ aQ) := by
 apply zXT
 · intro c
   simp only [bOe,CG,zTv,zQb]
   exact zPw znf (zG3 FX aZ aQ c)
 · intro i
   obtain ⟨i | i,rfl⟩:=(ziU (m:=2) (n:=2)).surjective i
   · rw [finSumFinEquiv_apply_left,bOg]
     fin_cases i <;> simp [CG]
   · rw [finSumFinEquiv_apply_right,bwR]
     fin_cases i <;> simp [CG,ek]
private theorem goR (i:Fin 2) (c:aZ) :
  (Vy i c).coeff 0=c:= by
 have h: (constantCoeff :zM1 aZ →+* aZ).comp (Vy i)=zz5 _:= by
  apply zXT
  · intro a
    simp [Vy]
  · intro j
    by_cases hji:j=i <;> simp [Vy,hji]
 exact zmU h c
private theorem goQ (i:Fin 2) (c:aZ) :
    (Vy i c).coeff 1=zWe i c:= by
  classical
  induction c using z5i with
  | C a=>simp [Vy]
  | add a b ha hb=>simp [map_add,ha,hb]
  | mul_X a j ha =>
    have hx :Vy i (z9v j) =
        C (z9v j:aZ)+if j=i then z7y else 0:= by
      simp [Vy]
    rw [zok,hx,zGW]
    by_cases hji:j=i
    · subst j
      have hcoef : (Vy i a*z7y).coeff 1=(Vy i a).coeff 0 :=
        coeff_mul_X (Vy i a) 0
      rw [zYp rfl,mul_add,coeff_add,coeff_mul_C,hcoef,
        ha,goR,MvPolynomial.pderiv_X_self,zqg]
    · rw [zND hji,z0a,coeff_mul_C,ha,MvPolynomial.pderiv_X_of_ne hji,
        mul_zero,z0a]
private theorem gt3 {A:Type*} [za6 A] (a :aZ →+* A) :
    (Ih a).comp (oi.comp pZ) =
      zDK (a.comp znf) := by
  apply zXT
  · intro c
    simp [oi,pZ,Ih]
  · intro i
    have hidx :Fin.castLE (by decide :3≤4) (Fin.castLE (by decide :2≤3) i) =
        zVs 2 i:=rfl
    simp only [zQb,oi,pZ,ziQ,
      zlv,z6l,z7N]
    rw [hidx,bOg]
private theorem eKR {A R:Type*} [CommSemiring A] [Semiring R]
  (i:Fin 2) (g:R →+* z3y (Fin 2) A) (x :A) (f :R[X]) :
  zWe i (f.eval₂ g (znf x)) =
    f.sum (fun j c=>zWe i (g c)*(znf x)^j) := by
 simp [zI6,zhr,zdo,zDE]
theorem gt4 {A:Type*} [za6 A] (a :aZ →+* A)
    (i:Fin 2) (P:Jet) :
    Ih a (iJ (A5 i 1 P)) =
      zWe i (Ih a (iJ P)) := by
  let t:=Ih a
  let e :aZ →+* z3y (Fin 2) A:=zDK (a.comp znf)
  let y :A:=a (z9v 0)
  let v :A:=a (z9v 1)
  let b:zS3 →+* z3y (Fin 2) A:=zqf e (znf y)
  have hroot :t.comp (oi.comp A7)=b:= by
    apply z86
    · intro c
      simp only [zQb,A7,b,z4Q,zJU]
      exact zLs (gt3 a) c
    · simp only [zQb,A7,b,z4Q,zC9,oi,
        ziQ,zlv,z6l]
      rw [show zQY (by decide :3≤4) (2 :Fin 3)=zzs 2 (0:Fin 2) from rfl]
      exact bwR a 0
  have hjetHom:t.comp iJ=zqf b (znf v) := by
    apply z86
    · intro Q
      simpa only [zQb,iJ,z4Q,zJU] using
        zLs hroot Q
    · simp only [zQb,iJ,z4Q,zC9]
      rw [show (3:Fin 4)=zzs 2 (1 :Fin 2) from rfl]
      exact bwR a 1
  have hjet (Q:Jet) :t (iJ Q) =
      Q.eval₂ b (znf v) :=
    zLs hjetHom Q
  have hInner (Q:zS3) :
      (Q.sum fun k c=>monomial k ((Vy i c).coeff 1)).eval₂
        e (znf y)=zWe i (Q.eval₂ e (znf y)) := by
    refine Eq.trans ?_ (eKR i e y Q).symm
    rw [eval₂_sum]
    apply zUo rfl
    intro k hk
    simp only [eval₂_monomial,goQ,e,MvPolynomial.pderiv_map]
  calc
    t (iJ (A5 i 1 P))=(A5 i 1 P).eval₂
        b (znf v) :=hjet _
    _=P.sum (fun j Q=>zWe i (b Q)*(znf v)^j) := by
      rw [A5,eval₂_sum]
      apply zUo rfl
      intro j hj
      simp only [eval₂_monomial,b,z4Q,hInner]
    _=zWe i (P.eval₂ b (znf v)) := by
      simp only [zI6,zhr,zdo]
      apply zUo rfl
      intro j _
      simp only [Derivation.leibniz,smul_eq_mul,Derivation.leibniz_pow,MvPolynomial.derivation_C,zero_mul,mul_zero,smul_zero,nsmul_zero,add_zero,zero_add,zDE]
    _=zWe i (t (iJ P)) :=zPw (zWe i) (hjet P).symm
private def bhg (P:Jet) :List (Fin 2)→Jet
 | []=>P
 | i :: t=>A5 i 1 (bhg P t)
private theorem ddV {h:ℕ} {rows :vP} {s :Shape}
   (hshift:qQ.bk4 h rows s) {W:ℕ} {P:Jet} (hP:P∈rows s W)
   (t:List (Fin 2)) :
   bhg P t∈rows s (W+2*h*t.length) := by
 induction t with
 | nil=>simpa [bhg] using hP
 | cons i t ih =>
   have hs :=hshift _ _ ih i 1
   simpa [bhg,Nat.mul_succ,zVg] using hs
private theorem dfc {A:Type*} [za6 A] (a :aZ →+* A)
   (P:Jet) (t:List (Fin 2)) :
   Ih a (iJ (bhg P t)) =
     aml (Ih a (iJ P)) t:= by
 induction t with
 | nil=>rfl
 | cons i t ih=>simp only [bhg,aml,gt4,ih]
end
end ac2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ac2
noncomputable section
open cu gT pI Polynomial
open scoped nonZeroDivisors
private theorem azW :
   Jl.toRingHom.comp qO=MvPolynomial.C:= by
 apply zXT
 · intro c
   simp [qO]
 · intro i
   change Jl ((zHw (zzs 2)) (z9v i))= _
   rw [z6l]
   exact bNE i
private theorem a8J {A:Type*} [za6 A] (q:aZ →+* A) (s :aZ) :
  Ih q (qO s)=znf (q s) := by
 have h:=zLs azW s
 change Jl (qO s)=znf s at h
 simp [Ih,h]
private def aOZ:tK →+* aZ :=
 zqf (zqf znf (z9v 0)) (z9v 1)
private theorem eFL:zpX aOZ:= by
 let e :aZ →+* tK :=
   zOD (C.comp C) ![C (z7y:zM1 FX),z7y]
 have he :aOZ.comp e=zz5 aZ:= by
   apply zXT
   · intro c
     simp [e,aOZ]
   · intro i
     fin_cases i <;> simp [e,aOZ]
 intro s
 exact ⟨e s,zLs he s⟩
private theorem epQ:C7=qO.comp aOZ:= by
  apply z86
  · intro f
    have h:C7.comp C=(qO.comp aOZ).comp C:= by
      apply z86
      · intro c
        simp [C7,Gw,qQ.Ng,iJ,A7,
          oi,pZ,qO,aOZ]
      · simp [C7,Gw,qQ.Ng,iJ,A7,
          oi,qO,aOZ,ziQ]
    exact zLs h f
  · simp [C7,Gw,qQ.Ng,iJ,qO,aOZ]
theorem b57 (I:znc z87) :
  (I.comap C7).map C7=(I.comap qO).map qO:= by
 rw [epQ,← zg6,← z0L,
  Ideal.map_comap_of_surjective _ eFL]
private theorem cqq {A:Type*} [za6 A] (q:aZ →+* A) :
  zdq (Ih q)=(zdq q).map qO:= by
 rw [Ih,← zEW,zRA,← azW,
  ← z0L,
  zFA Jl.toRingHom Jl.bijective]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem afo {A:Type*} [za6 A] [zue A]
   (q:aZ →+* A) (hq:zpX q) (J:znc z87) (f :z87)
   (hf :Ih ((z12 A (zNv A)).comp q) f ∈
     J.map (Ih ((z12 A (zNv A)).comp q))) :
   ∃ s :aZ,q s≠0∧qO s*f∈J ⊔ (zdq q).map qO:= by
 let e :=Ih q
 let a :=z12 (z3y (Fin 2) A) (z3y (Fin 2) (zNv A))
 have he :zpX e :=
   (z6h _ hq).comp Jl.surjective
 have hcomp:Ih ((z12 A (zNv A)).comp q)=a.comp e := by
   apply zz4
   intro f
   change zDK ((z12 A (zNv A)).comp q) (Jl f)= _
   rw [← z6Y]
   rfl
 rw [hcomp,← z0L] at hf
 change a (e f)∈(J.map e).map a at hf
 obtain ⟨_,⟨d,hd,rfl⟩,hmem⟩ :=
   (IsLocalization.algebraMap_mem_map_algebraMap_iff
     ((zgt A).map (znf (σ:=Fin 2))) _ (J.map e) (e f)).mp hf
 obtain ⟨s,hs⟩:=hq d
 rw [← hs,← a8J,← zok] at hmem
 rw [← Ideal.mem_comap,zEk _ he,
   ← zPx,cqq] at hmem
 exact ⟨s,hs.symm ▸ zyw hd,hmem⟩
theorem dLt {I:znc z87} (hd:dual I) {m:ℕ} {P:Jet}
    (hf :CG (iJ P)∈(I.map CG)^m) :
    O9 I P m:= by
  have hproper :I.map CG ≠ ⊤ := by
    intro ht
    have hsub:zOt (Lj I) := by
      change zOt (gk (I.map CG))
      rw [ht]
      infer_instance
    exact (Nat.ne_of_gt hd) zuF
  rw [← zXb,aVL] at hf
  have h:=afo (zz5 aZ) Function.surjective_id (I ^m) (iJ P)
    (by simpa only [RingHom.comp_id] using hf)
  obtain ⟨s,hs,hmem⟩:=h
  have hnot:qO s∉I:= by
    intro hin
    apply hproper
    have hm:=z7X CG hin
    rw [aVL,a8J] at hm
    rw [aVL]
    apply zAn _ hm
    have hz :z12 aZ aQ s≠0:= by
      intro he
      apply hs
      exact (zxb aZ aQ)
        (he.trans ((z12 aZ aQ).map_zero).symm)
    exact (isUnit_iff_ne_zero.mpr hz).map znf
  refine ⟨qO s,hnot,?_⟩
  simpa [hd,zPx] using hmem
theorem dLB {I:znc z87} (hp:I.IsPrime) (hd : ¬ dual I) {m:ℕ} {P:Jet}
   (hf :T3 I (iJ P)∈(I.map (T3 I))^m) :
   O9 I P m:= by
 classical
 let _:I.IsPrime :=hp
 have hj: (I.comap qO).IsPrime :=zCL qO
 let _:zue (agI I) :=Ideal.Quotient.nontrivial_iff.mpr hj.ne_top
 let q:aZ →+* agI I:=zVv (I.comap qO)
 have hq:zpX q:=zld
 have hclear :=afo (A:=agI I) q hq (I ^m) (iJ P)
 have hspec :Ih ((z12 (agI I) (Tw I)).comp q) =
     T3 I:=rfl
 rw [hspec,zXb] at hclear
 obtain ⟨s,hs,hmem⟩:=hclear hf
 have hnot:qO s∉I:= fun hin =>
   hs (Ideal.Quotient.eq_zero_iff_mem.mpr hin)
 refine ⟨qO s,hnot,?_⟩
 change qO s*iJ P∈I ^m ⊔
   (if dual I then ⊥ else (I.comap C7).map C7)
 rw [zND hd,b57]
 change qO s*iJ P∈I ^m ⊔
   (zdq (zVv (I.comap qO))).map qO at hmem
 rwa [zlC] at hmem
end
end ac2
end
section
namespace ac2
noncomputable section
open K1 MvPolynomial
private theorem natCast_ne_zero {A:Type*} [zrb A] [zLw A p] {n:ℕ}
  (hpos :0<n) (hn:n<p) : (n:A)≠0:= by
 intro hz
 exact (ziF hn) (zTm hpos ((zX2 _ _ _).mp hz))
private theorem bFB {A:Type*} [zrb A] [zLw A p]
   {g:z3y (Fin 2) A} (hg:Prime g) (hdeg:g.totalDegree<p) :
   ∃ i:Fin 2,¬ g∣zWe i g:= by
 have hv :g.vars.Nonempty := by
   by_contra! he
   have heq :=vars_eq_empty_iff_eq_C.mp he
   have hn:g.coeff 0≠0:= by
     intro hz
     exact hg.ne_zero (by rw [heq,hz,zhc])
   exact hg.not_isUnit (heq ▸ (isUnit_iff_ne_zero.mpr hn).map C)
 obtain ⟨i,hi⟩:=hv
 have hpos :=zOl (mem_vars_iff_degreeOf_ne_zero.mp hi)
 have hc: (g.degreeOf i:A)≠0 :=
   natCast_ne_zero hpos ((degreeOf_le_totalDegree g i).trans_lt hdeg)
 have hn:=pderiv_ne_zero_of_natCast_ne_zero i g hc
 have hb:=degreeOf_pderiv_le_sub_one i g
 refine ⟨i,?_⟩
 rintro ⟨f,h⟩
 have hf :f≠0:= by
   intro hf
   exact hn (by rw [h,hf,mul_zero])
 rw [h,degreeOf_mul_eq hg.ne_zero hf] at hb
 omega
private theorem epm {A:Type*} [zrb A] [zLw A p] (i:Fin 2)
   {g:z3y (Fin 2) A} (hg:Prime g) (hsep : ¬ g∣zWe i g)
   (a :ℕ) (ha :a<p) {f :z3y (Fin 2) A} (hf : ¬ g∣f) :
   ¬ g∣(zWe (R:=A) i)^[a] (g^a*f) := by
 induction a generalizing f with
 | zero=>simpa using hf
 | succ a ih =>
   let v :=((a+1 :ℕ) :z3y (Fin 2) A)*(zWe i g*f)+g*zWe i f
   have hstep:zWe i (g^(a+1)*f)=g^a*v := by
     rw [zGW,pderiv_pow,Nat.add_sub_cancel,zVI g a]
     dsimp only [v]
     ring
   have hu:zWB ((a+1 :ℕ) :z3y (Fin 2) A) := by
     rw [← map_natCast (C:A →+* z3y (Fin 2) A)]
     exact (isUnit_iff_ne_zero.mpr (natCast_ne_zero (Nat.succ_pos a) ha)).map C
   have hv : ¬ g∣v := by
     intro hd
     have hd' := (dvd_add_left (dvd_mul_right g (zWe i f))).mp hd
     exact (hg.dvd_or_dvd (hu.dvd_mul_left.mp hd')).elim hsep hf
   rw [Function.iterate_succ_apply,hstep]
   exact ih (zws ha) hv
private theorem eKG {A:Type*} [zrb A] (f :z3y (Fin 2) A)
   (i:Fin 2) (a :ℕ) :
   aml f (List.replicate a i)=(zWe (R:=A) i)^[a] f := by
 induction a with
 | zero=>rfl
 | succ a ih =>
   rw [List.replicate_succ,aml,ih,Function.iterate_succ_apply']
theorem dXr {A:Type*} [zrb A] [zLw A p] {g f :z3y (Fin 2) A}
  (hg:Prime g) (hdeg:g.totalDegree<p) {r :ℕ} (hr :r<p)
  (hf :bp3 (zye {g}) f r) :
  f∈zye ({g} : Set (z3y (Fin 2) A))^(r+1) := by
 classical
 rw [zNi,zxV]
 by_contra hpow
 obtain ⟨i,hi⟩:=bFB hg hdeg
 have hex : ∃ n:ℕ,¬ g^n∣f :=⟨r+1,hpow⟩
 have hpos :0<zqr hex := by
  by_contra! hn
  have hz :zqr hex=0:= by omega
  exact zWq hex (by simp [hz])
 let a :=zqr hex - 1
 have ha :a+1=zqr hex :=zxt hpos
 have har :a≤ r := by
  have hle :=Nat.find_min' hex hpow
  omega
 obtain ⟨u,he⟩:g^a∣f :=
  not_not.mp (Nat.find_min hex (by omega :a<Nat.find hex))
 have hu : ¬ g∣u:= by
  rintro ⟨z,rfl⟩
  apply zWq hex
  rw [← ha,he,zVI,← ztg]
  exact dvd_mul_right _ _
 have hd:=hf (List.replicate a i) (by simpa using har)
 rw [eKG,he,zxV] at hd
 exact epm i hg hi a (har.trans_lt hr) hu hd
end
end ac2
end
section
namespace ac2
noncomputable section
open K1 cu gT pI
def c1 :Prop :=
  ∀ I:znc z87,I.IsPrime →
    zAa aQ (Lj I)→dual I →
    zsE aQ (Lj I)<p →
    ∀ (f :vR) (r :ℕ),r<p →
      bp3 (I.map CG) f r →
      f∈(I.map CG)^(r+1)
def c2 :Prop :=
  ∀ I:znc z87,xN I → ¬ dual I →
    ∃ g:z3y (Fin 2) (Tw I),
      Prime g∧g.totalDegree<p∧I.map (T3 I)=zye {g}
end
end ac2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace aR0
noncomputable section
open cu gT pI ac2
open scoped Polynomial nonZeroDivisors
private theorem azW :
   Jl.toRingHom.comp qO=MvPolynomial.C:= by
 apply zXT
 · intro c
   simp [qO]
 · intro i
   change Jl ((zHw (zzs 2)) (z9v i))= _
   rw [z6l]
   exact bNE i
private theorem a8J {A:Type*} [za6 A]
  (q:aZ →+* A) (s :aZ) :
  Ih q (qO s)=znf (q s) := by
 have h:=zLs azW s
 change Jl (qO s)=znf s at h
 simp [Ih,h]
private theorem cqq {A:Type*} [za6 A] (q:aZ →+* A) :
  zdq (Ih q)=(zdq q).map qO:= by
 rw [Ih,← zEW,zRA,← azW,
  ← z0L,
  zFA Jl.toRingHom Jl.bijective]
private theorem epM:zq4 qO:= by
 intro a b h
 apply zbo (Fin 2) aZ
 exact (zLs azW a).symm.trans
  ((zPw Jl.toRingHom h).trans (zLs azW b))
def aD4 (I:znc z87) :FX[X] →ₐ[FX] agI I :=
 zEU (zVv (I.comap qO) (z9v 0))
theorem c2Q {I:znc z87} (hI:xN I) :
   zq4 (aD4 I) := by
 let u:FX[X] →+* aZ :=
   zqf znf (z9v 0)
 have h:qO.comp u=F7:= by
   apply z86
   · intro c
     simp [qO,u,F7]
   · simp [qO,u,F7]
 have hn: (aD4 I).toRingHom=(zVv _).comp u:= by
   apply z86
   · intro c
     simp [aD4,u]
     rfl
   · simp [aD4,u]
 apply (zli _).mpr
 rw [RingHom.ker_eq_bot_iff_eq_zero]
 intro a ha
 change (aD4 I).toRingHom a=0 at ha
 rw [hn,zQb,z1Q] at ha
 have hz : ((zVv I).comp F7) a=0:= by
   rw [← h]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
 exact hI.ordinate_dominant (hz.trans (zhc _).symm)
private theorem enJ {I:znc z87} (hI:xN I)
   [I.IsPrime] :1≤ zqe (agI I) := by
 let B:=agI I
 let: (I.comap qO).IsPrime :=zG1 qO I
 have hfield : ¬ IsField B:= by
   intro h
   let:zrb B:=h.toField
   let:zAa FX B:=finite_of_finite_type_of_isJacobsonRing FX B
   exact Polynomial.not_finite (Module.Finite.of_injective
     (aD4 I).toLinearMap (c2Q hI))
 obtain ⟨P,hP,_⟩:=(⊥ : znc B).exists_le_maximal bot_ne_top
 let:P.IsPrime :=hP.isPrime
 have hne : (⊥ : znc B)≠P:= fun h =>
   hfield (Ring.isField_iff_maximal_bot.mpr (h.symm ▸ hP))
 have hlt: (⊥ : znc B)<P:=bot_lt_iff_ne_bot.mpr hne.symm
 have hlo:1≤P.height:= by
   simpa [Ideal.height_bot] using zSK hlt
 exact (WithBot.coe_le_coe.mpr hlo).trans (ztp (I:=P))
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem enE {I:znc z87} (hI:xN I) (hd : ¬ dual I)
   [I.IsPrime] :I.comap qO ≠ ⊥ := by
 intro hbot
 let Q:=I.map Jl.toRingHom
 have hbase :Q.comap znf=I.comap qO:= by
   rw [← azW,← zg6,
     zFA Jl.toRingHom Jl.bijective]
 let S:=(zgt aZ).map (znf (σ:=Fin 2))
 have hdisj:z1v (S:Set (z3y (Fin 2) aZ))
     (Q:Set (z3y (Fin 2) aZ)) := by
   rw [zM4]
   rintro _ ⟨d,hd,rfl⟩ hm
   have he :d∈Q.comap MvPolynomial.C:=hm
   rw [hbase,hbot] at he
   exact zyw hd (Ideal.mem_bot.mp he)
 have hproper :=(z78
   (S:=z3y (Fin 2) aQ) _ Q).mpr hdisj
 have he :Q.map (z12 (z3y (Fin 2) aZ)
     (z3y (Fin 2) aQ))=I.map CG:= by
   rw [aVL,Ih,← z0L]
   rfl
 rw [he] at hproper
 let:zue (Lj I) :=Ideal.Quotient.nontrivial_iff.mpr hproper
 let:zAa aQ (Lj I) :=hI.jet_finite
 exact hd zRt
private theorem eKd {I:znc z87} (hI:xN I) [I.IsPrime] :
   I.height≤2 := by
 let x :zy6 Ambient:=⟨I,zWv⟩
 have hc:Order.coheight x=2 := by
   have h:=hI.dimension
   rw [ringKrullDim_quotient] at h
   change Order.krullDim (Set.Ici x)=2 at h
   rw [← Order.coheight_eq_krullDim_Ici] at h
   exact WithBot.coe_injective h
 have hd:zqe z87=4 := by
   simp [zZT]
 have hh: (↑(Order.height x+Order.coheight x) :zUi ℕ∞)≤ zqe Ambient:= by
   rw [zqe,Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
   exact WithBot.coe_le_coe.mpr (le_iSup (fun y :zy6 z87 =>
     Order.height y+Order.coheight y) x)
 rw [hc,← x.height_eq_orderHeight,hd] at hh
 have hh' : I.height+2≤(2 :ℕ∞)+2 :=WithBot.coe_le_coe.mp hh
 exact (ENat.add_le_add_iff_right (by simp : (2 :ℕ∞) ≠ ⊤)).mp hh'
theorem eN5 {I:znc z87} (hI:xN I) (hd : ¬ dual I) :
   ∃ g:z3y (Fin 2) (Tw I),
     Prime g∧I.map (T3 I)=zye {g} := by
 let:I.IsPrime :=hI.prime
 let P:=I.comap qO
 let:P.IsPrime :=zG1 qO I
 let B:=agI I
 let D:=z3y (Fin 2) B
 let E :=z3y (Fin 2) (Tw I)
 let q:aZ →+* B:=zVv P
 let e :z87 →+* D:=Ih q
 let a :D →+* E :=z12 D E
 let Q:=I.map e
 let J:=I.map (T3 I)
 let S:=(zgt B).map (znf (σ:=Fin 2))
 have he :zpX e :=
   (z6h _ zld).comp Jl.surjective
 have hk :zdq e=P.map qO:= by
   rw [cqq,zlC]
 have hkle :zdq e≤I:= by
   rw [hk]
   exact Ideal.map_comap_le
 have hQcomap :Q.comap e=I:= by
   rw [zEk _ he,← zPx,sup_of_le_left hkle]
 have hQa :J= Q.map a := by
   change J=(I.map e).map a
   rw [z0L]
   change I.map (Ih ((z12 B (Tw I)).comp q))=I.map (a.comp e)
   congr 1
   apply zz4
   intro f
   change zDK ((z12 B (Tw I)).comp q) (Jl f) =
     zDK (z12 B (Tw I)) (zDK q (Jl f))
   rw [z6Y]
 have hQ:Q.IsPrime :=Ideal.map_isPrime_of_surjective he hkle
 have hS:z1v (S:Set D) (Q:Set D) := by
   rw [zM4]
   rintro _ ⟨d,hd,rfl⟩ hm
   obtain ⟨s,rfl⟩:=zld (I:=P) d
   have hm' : qO s∈Q.comap e := by
     change Ih q (qO s)∈Q
     rwa [a8J]
   rw [hQcomap] at hm'
   exact zyw hd (Ideal.Quotient.eq_zero_iff_mem.mpr hm')
 have hJ:J.IsPrime := by
   rw [hQa]
   exact znL S E Q hQ hS
 have hJa :J.comap a= Q:= by
   rw [hQa]
   exact ztT S E hQ hS
 have ha :zq4 a :=
   zNV _ (zxb B (Tw I))
 have hJn:J ≠ ⊥ := by
   intro hz
   have hQ0:Q = ⊥ := by
     rw [← hJa,hz,zes _ ha]
   have hIker :zdq e=I:= by
     rw [zPx,← hQ0,hQcomap]
   let eq :gk I ≃+* D :=
     (Ideal.quotEquivOfEq hIker.symm).trans (e.quotientKerEquivOfSurjective he)
   have hdim:=ringKrullDim_eq_of_ringEquiv (R:=gk I) (S:=D) eq
   rw [hI.dimension] at hdim
   have hpoly :=zbi (R:=B) (Fin 2)
   rw [zJa,← hdim] at hpoly
   have hlo: (1 :zUi ℕ∞)+2≤2 :=
     (zZP (enJ hI) (le_refl (2 :zUi ℕ∞))).trans hpoly
   exact (by decide : ¬ (1 :WithBot ℕ∞)+2≤2) hlo
 have hk0: (⊥ : znc z87)<zdq e := by
   obtain ⟨d,hdP,hd0⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (enE hI hd)
   apply bot_lt_iff_ne_bot.mpr
   intro h
   have hm:=z7X qO hdP
   rw [← hk,h,Ideal.mem_bot] at hm
   exact hd0 (epM (hm.trans (zhc _).symm))
 let:zsh (Tw I) :=PrincipalIdealRing.to_uniqueFactorizationMonoid
 let:zsh E :=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 obtain ⟨g,hgJ,hg⟩:=Ideal.IsPrime.exists_mem_prime_of_ne_bot hJ hJn
 refine ⟨g,hg,zWs ?_ ((zvl _).mpr hgJ)⟩
 by_contra hn
 let G:znc E :=zye {g}
 let K:=(G.comap a).comap e
 have hG:G.IsPrime :=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
 have hK:K.IsPrime :=zG1 e _
 have hlt:G<J:=zXi ((zvl _).mpr hgJ)
   (fun h=>hn h.ge)
 have hmap :StrictMono (zK3 a) := by
   intro U W h
   have hinv (T:znc E) : (T.comap a).map a=T:=IsLocalization.map_under S E T
   exact zXi (Ideal.comap_mono h.le) fun hm =>
     h.ne ((hinv U).symm.trans ((zPw (Ideal.map a) hm).trans (hinv W)))
 have he' : StrictMono (zK3 e) := by
   intro U W h
   exact zXi (Ideal.comap_mono h.le)
     (fun hm=>h.ne (Ideal.comap_injective_of_surjective e he hm))
 have hKI:K<I:= by
   rw [← hQcomap,← hJa]
   exact he' (hmap hlt)
 have hbotG: (⊥ : znc E)<G :=
   bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr hg.ne_zero)
 have hkK:zdq e<K:= by
   rw [zPx]
   have h:=hmap hbotG
   change (⊥ : znc E).comap a<G.comap a at h
   rw [zes _ ha] at h
   exact he' h
 have : (zdq e).IsPrime :=zgL e
 have h1 :=zSK hk0
 have h2 :=zSK hkK
 have h3:=zSK hKI
 have hlo: (3:ℕ∞)≤I.height:= calc
   (3:ℕ∞)=(⊥ : znc z87).height+1+1+1 := by
     rw [Ideal.height_bot]
     decide
   _≤(zdq e).height+1+1 :=zZP (zZP h1 zs1) zs1
   _≤K.height+1 :=zZP h2 zs1
   _≤I.height:=h3
 exact (by decide : ¬ (3:ℕ∞)≤2) (hlo.trans (eKd hI))
end
end aR0
end
section
namespace cy0
noncomputable section
open K1 cu gT pI ac2 MvPolynomial
open scoped nonZeroDivisors
private theorem natCast_ne_zero {A:Type*} [zrb A] [zLw A p] {n:ℕ}
  (hpos :0<n) (hlt:n<p) : (n:A)≠0:= by
 intro h
 exact (ziF hlt) (zTm hpos ((zX2 _ _ _).mp h))
private theorem cpe {A E :Type*} [zrb A] [zrb E] [zLw A p]
  [zZE A E] [zAa A E] (hsize :zsE A E<p) :
  Algebra.IsSeparable A E := by
 constructor
 intro x
 have hx :zsq A x :=zmn x
 let f :=minpoly A x
 have hpos :0<f.natDegree :=zGQ hx
 have hlt:f.natDegree<p:=(z48 x).trans_lt hsize
 change f.Separable
 apply (zKY (zy4 hx)).2
 intro hzero
 obtain ⟨n,hn⟩:=zwS hpos.ne'
 have hcoeff :=zPw (fun q:zM1 A=>q.coeff n) hzero
 change f.derivative.coeff n=(0:zM1 A).coeff n at hcoeff
 have hmonic:f.coeff f.natDegree=1 :=(minpoly.monic hx).leadingCoeff
 rw [hn] at hmonic
 rw [zMD,zO6,← zg0,
  ← hn,hmonic,zkF] at hcoeff
 exact natCast_ne_zero hpos hlt hcoeff
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem ep7 {I:znc z87} (hI:I.IsPrime) (hd:dual I) :
  (I.map CG).IsPrime := by
 let R:=z3y (Fin 2) aZ
 let S:zdT R:=(zgt aZ).map znf
 let J:=I.map Jl.toRingHom
 have hJ:J.IsPrime := by
  change (I.map (Jl:z87 →+* R)).IsPrime
  rw [Ideal.map_comap_of_equiv Jl]
  exact hI.comap _
 have hm:I.map CG=J.map (z12 R vR) := by
  rw [z0L,aVL]
  rfl
 have hproper :I.map CG ≠ ⊤ := by
  intro ht
  let:zOt (Lj I) :=Ideal.Quotient.subsingleton_iff.mpr ht
  exact (Nat.ne_of_gt hd) (z6g aQ (Lj I))
 have hdisj:z1v (S:Set R) (J:Set R) :=
  (z78 S vR J).mp (hm ▸ hproper)
 rw [hm]
 exact znL S vR J hJ hdisj
private def translate {A:Type*} [za6 A] (a :Fin 2→A) :
  z3y (Fin 2) A →+* z3y (Fin 2) A :=
 zOD C (fun i=>z9v i+C (a i))
private theorem bh9 {A:Type*} [za6 A] (a :Fin 2→A)
   (f :z3y (Fin 2) A) (i:Fin 2) :
   translate a (zWe i f)=zWe i (translate a f) := by
 classical
 induction f using z5i with
 | C c=>simp [translate]
 | add f g hf hg=>simp [hf,hg]
 | mul_X f j hf =>
   rw [zGW,zrl,zok,zok,hf,zok,zGW]
   by_cases hj:j=i
   · subst j
     simp [translate]
   · simp [translate,pderiv_X_of_ne hj]
private theorem gDO {A E :Type*} [za6 A] [za6 E]
   (c:A →+* E) (a :Fin 2→E) (f :z3y (Fin 2) A) (t:List (Fin 2)) :
   aml (translate a (map c f)) t=translate a (map c (aml f t)) := by
 induction t with
 | nil=>rfl
 | cons i t ih=>rw [aml,aml,ih,← bh9,pderiv_map]
private theorem eKH {A:Type*} [za6 A] (f :z3y (Fin 2) A)
   (i:Fin 2) (t:List (Fin 2)) :
   aml f (t ++ [i])=aml (zWe i f) t:= by
 induction t with
 | nil=>rfl
 | cons j t ih=>simp only [List.cons_append,aml,ih]
private theorem eH9 {E :Type*} [za6 E]
   (hunit : ∀ n:ℕ,0<n→n<p→ zWB (n:E)) (r :ℕ)
   (hr :r<p) (f :z3y (Fin 2) E)
   (hf : ∀ t:List (Fin 2),t.length≤ r→(aml f t).coeff 0=0) :
   f∈idealOfVars (Fin 2) E^(r+1) := by
 classical
 induction r generalizing f with
 | zero =>
   apply (z7v _ _).mpr
   intro m hm
   have hz :m=0:=(Finsupp.degree_eq_zero_iff m).mp (by omega)
   subst m
   exact hf [] (by simp)
 | succ r ih =>
   apply (z7v _ _).mpr
   intro m hm
   by_cases hz :m=0
   · subst m
     exact hf [] (by simp)
   obtain ⟨i,hi⟩:=Finsupp.ne_iff.mp hz
   change m i≠0 at hi
   have hs :Finsupp.single i 1≤ m:=Finsupp.single_le_iff.mpr (zOl hi)
   obtain ⟨k,hk⟩:=le_iff_exists_add'.mp hs
   have hdeg:m.degree=k.degree+1 := by rw [hk,zrl,Finsupp.degree_single]
   have hsmall:k.degree< r+1 := by omega
   have hmem:=ih (zws hr) (zWe i f) (fun t ht=> by
     rw [← eKH]
     apply hf
     simpa using Nat.succ_le_succ ht)
   have hc:=(z7v _ _).mp hmem k hsmall
   rw [coeff_pderiv,← hk] at hc
   have hcast:zWB ((k i:E)+1) := by
     rw [← zg0]
     apply hunit _ (Nat.succ_pos _)
     have hle :=Finsupp.le_degree i k
     omega
   exact hcast.mul_left_eq_zero.mp hc
set_option maxHeartbeats 500000 in
private theorem dPn {A:Type*} [zrb A] [zLw A p]
    (J:znc (z3y (Fin 2) A))
    [Algebra.FormallySmooth A (z3y (Fin 2) A ⧸ J)]
    (f :z3y (Fin 2) A) (r :ℕ) (hr :r<p) (hf :bp3 J f r) :
    f∈J^(r+1) := by
  let R:=z3y (Fin 2) A
  let E :=R ⧸ J
  let B:=R ⧸ J^(r+1)
  let q:R →ₐ[A] E :=zvR A J
  let b:R →ₐ[A] B:=zvR A (J^(r+1))
  have hle :J^(r+1)≤J:=Ideal.pow_le_self (Nat.succ_ne_zero r)
  let g:B →ₐ[A] E :=z5F A hle
  have hker :zdq g=J.map b:= by
    change zdq (Ideal.Quotient.factor hle)=J.map (zVv _)
    calc
      _=(zdq (zVv J)).map (zVv (J^(r+1))) :=
        Ideal.ker_quotient_lift (zVv J) _
      _ = _:= by rw [zlC]
  have hnil: (zdq g)^(r+1) = ⊥ := by
    rw [hker,← zXb]
    exact Ideal.map_quotient_self (J^(r+1))
  have hn:IsNilpotent (zdq g) :=⟨r+1,hnil⟩
  have hg:zpX g:=zuo hle
  let s :=Algebra.FormallySmooth.liftOfSurjective (zhD A E) g hg hn
  have hs (x :E) :g (s x)=x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (zhD A E) g hg hn x
  let a (i:Fin 2) :=q (z9v i)
  let F:=translate a (map (z12 A E) f)
  have he : (constantCoeff.comp ((translate a).comp (map (z12 A E))))=q.toRingHom:= by
    apply zXT
    · intro c
      simp [translate,q,E,R,← zKm]
    · intro i
      simp [translate,a]
  have hunit (n:ℕ) (hpos :0<n) (hlt:n<p) :zWB (n:E) := by
    rw [← map_natCast (z12 A E)]
    exact (isUnit_iff_ne_zero.mpr (natCast_ne_zero hpos hlt: (n:A)≠0)).map (z12 A E)
  have hF:F∈idealOfVars (Fin 2) E^(r+1) := by
    refine eH9 hunit r hr F ?_
    intro t ht
    change constantCoeff (aml F t)=0
    rw [show F=translate a (map (z12 A E) f) from rfl,gDO]
    change (constantCoeff.comp ((translate a).comp (map (z12 A E)))) (aml f t)=0
    rw [he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf t ht)
  let w (i:Fin 2) :=b (z9v i) - s (a i)
  let ev :z3y (Fin 2) E →+* B:=zOD s.toRingHom w
  have hw: (idealOfVars (Fin 2) E).map ev≤zdq g:= by
    rw [zo0,Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    change g (ev (z9v i))=0
    rw [show ev (z9v i)=w i by simp [ev]]
    change g (b (z9v i) - s (a i))=0
    rw [zpO,hs]
    exact sub_self (a i)
  have hzero :ev F=0:= by
    have hm:=z7X ev hF
    rw [zXb] at hm
    have hm' : ev F∈(zdq g)^(r+1) :=(pow_left_mono (r+1) hw) hm
    rw [hnil] at hm'
    exact Ideal.mem_bot.mp hm'
  have hcomp: (ev.comp (translate a)).comp (map (z12 A E))=b.toRingHom:= by
    apply zXT
    · intro c
      simp only [zQb,zpw,translate,ev,zTv]
      change s (z12 A E c)=b (C c)
      rw [s.commutes,← zKm,b.commutes]
    · intro i
      simp [translate,ev,w]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change b f=0
  exact (zLs hcomp f).symm.trans hzero
theorem proof :ac2.c1 := by
 intro I hI hfinite hd hsize f r hr hf
 let J:=I.map CG
 let:J.IsPrime :=ep7 hI hd
 let:zAa aQ (vR ⧸ J) :=hfinite
 let:zrb (vR ⧸ J) :=fieldOfFiniteDimensional aQ _
 let:zLw aQ p:=zgG
  ((z12 FX aQ).comp jz).injective p
 let:zw7 aQ (vR ⧸ J) :=cpe hsize
 let:Algebra.FormallyEtale aQ (vR ⧸ J) :=
  Algebra.FormallyEtale.of_isSeparable aQ (vR ⧸ J)
 exact dPn J f r hr hf
end
end cy0
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace akR
noncomputable section
open cu gT pI Polynomial
def bJ2 (G:tK) :dV[X] :=
 G.map (zqf (z12 FX dV) (kz 3))
def bJh (G:tK) :dV[X] :=
  G.eval₂
    (zqf (Polynomial.C.comp (z12 FX dV))
      (z1z (kz 3)-Polynomial.C (kz 1) *
        (z7y:dV[X])))
    (z7y:dV[X])
abbrev aRM (I:znc z87) :=
 gk (R:=tK) (I.comap C7)
def apn (I:znc z87) :
    z3y (Fin 3) (aRM I) →+* z3y (Fin 2) (gk I) :=
  zOD
    (MvPolynomial.C.comp (z3G I C7 zs1))
    ![z9v 0,z9v 1,
      znf (zVv I (z9v 0)) +
       z9v 0*znf (zVv I (z9v 1))]
end
end akR
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace akR
noncomputable section
open cu gT pI Polynomial
open scoped BigOperators
theorem cbn (i:Fin 4) :
   zq4 (zqf (z12 FX dV) (kz i)) := by
 let e :FX[X] →+* z3y (Fin 4) FX:=zqf znf (z9v i)
 let r :z3y (Fin 4) FX →+* FX[X] :=zOD z1z fun _=>(z7y:FX[X])
 have hr :r.comp e=zz5 _:= by
   apply z86
   · intro a
     simp [r,e]
   · simp [r,e]
 have hh:zqf (z12 FX dV) (kz i) =
     (z12 (z3y (Fin 4) FX) dV).comp e := by
   apply z86
   · intro a
     simp only [zQb,e,z4Q,zJU]
     exact zG3 FX (z3y (Fin 4) FX) dV a
   · simp [e,kz]
 have he :zq4 e :=
   (show Function.LeftInverse r e from fun p=>zLs hr p).injective
 rw [hh]
 exact (zxb (z3y (Fin 4) FX) dV).comp he
theorem eHR (G:tK) :
  (bJ2 G).natDegree=G.natDegree :=
 zt8 (cbn 3) _
theorem eAJ {G:tK} (hG:G≠0) {j i:ℕ}
    (hij: (G.coeff j).coeff i≠0) :i+j≤(bJh G).natDegree := by
  classical
  let k :=z12 FX dV
  let a :=kz 1
  let b:=kz 3
  let z :dV[X] :=C b - C a*(z7y:dV[X])
  let e :FX[X] →+* dV[X] :=zqf (C.comp k) z
  have ha :a≠0:= by
    have h:=(cbn 1).ne (X_ne_zero (R:=FX))
    simpa [a] using h
  have hz :z.natDegree=1 := by
    change (C b - C a*(z7y:dV[X])).natDegree=1
    rw [sub_eq_add_neg,add_comm,← neg_mul,← map_neg]
    exact natDegree_linear (neg_ne_zero.mpr ha)
  have hz' : z.leadingCoeff = -a := by
    rw [leadingCoeff,hz]
    simp [z,coeff_mul_X]
  have he (p:FX[X]) :e p=(p.map k).comp z := by
    change p.eval₂ (C.comp k) z= _
    rw [Polynomial.comp,zem]
  have hd (p:FX[X]) : (e p).natDegree=p.natDegree := by
    rw [he,natDegree_comp,hz,zqg,zt8 k.injective]
  have hcoeff (p:FX[X]) (n:ℕ) (hpn:p.natDegree≤n) :
      (e p).coeff n=k (p.coeff n*(-1)^n)*a^n:= by
    by_cases hp:p.natDegree=n
    · subst n
      calc
        (e p).coeff p.natDegree=(e p).leadingCoeff := by rw [leadingCoeff,hd]
        _=k (p.coeff p.natDegree)*(-a)^p.natDegree := by
          rw [he,leadingCoeff_comp (by simp [hz]),hz',leadingCoeff_map,
            zt8 k.injective,coeff_natDegree]
        _=k (p.coeff p.natDegree*(-1)^p.natDegree)*a^p.natDegree := by
          rw [zok,zkq,map_neg,zXs,ztg,← mul_pow,neg_one_mul]
    · have hp' : p.natDegree<n:=zXi hpn hp
      rw [zQl (by rwa [hd]),zQl hp']
      simp
  let D:=G.support.sup (fun v=>(G.coeff v).natDegree+v)
  have hD (v :ℕ) (hv :v∈G.support) : (G.coeff v).natDegree+v≤D :=
    Finset.le_sup (f := fun v=>(G.coeff v).natDegree+v) hv
  obtain ⟨v₀,hv₀,hD₀⟩:=G.support.exists_mem_eq_sup (support_nonempty.mpr hG)
    (fun v=>(G.coeff v).natDegree+v)
  change D =(G.coeff v₀).natDegree+v₀ at hD₀
  set top:FX[X] := ∑ v∈G.support,
    monomial (D-v) ((G.coeff v).coeff (D-v)*(-1)^(D-v)) with htopDef
  have htop:top≠0:= by
    have htop' : top.coeff (D - v₀)≠0:= by
      rw [htopDef,finsetSum_coeff,Finset.sum_eq_single_of_mem v₀ hv₀]
      · rw [coeff_monomial_same,show D - v₀=(G.coeff v₀).natDegree by omega,
          coeff_natDegree]
        exact zBS (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hv₀))
          (zm1 _ (neg_ne_zero.mpr zOR))
      · intro v hv hne
        have :=hD v hv
        exact coeff_monomial_of_ne _ (by omega)
    intro h
    exact htop' (by simp [h])
  let t:=zqf k a
  have ht:t top≠0:= by
    have h:t top≠t 0:=(cbn 1).ne htop
    simpa only [zhc] using h
  have hcoeffD: (bJh G).coeff D =t top:= by
    change (G.eval₂ e (z7y:dV[X])).coeff D =t top
    rw [zI6,zhr,finsetSum_coeff,htopDef,zdo]
    apply zUo rfl
    intro v hv
    have hb:=hD v hv
    rw [coeff_mul_X_pow',zYp (show v≤D by omega),hcoeff _ _ (by omega)]
    simp [t,eval₂_monomial]
  have hDle :D ≤(bJh G).natDegree :=
    le_natDegree_of_ne_zero (hcoeffD.trans_ne ht)
  have hj:j∈G.support := by
    apply mem_support_iff.mpr
    intro h
    exact hij (by simp [h])
  exact ((zlr (le_natDegree_of_ne_zero hij) j).trans (hD _ hj)).trans hDle
end
end akR
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace akR
noncomputable section
open cu gT pI Polynomial
open scoped nonZeroDivisors
private def azk :aZ →+* Ambient :=
 (zHw (fun i:Fin 2=>(zQY (by decide :2≤4) i)+2)).toRingHom
private def ctH :aZ →+* tK :=
 zOD
  ((z1z:FX[X] →+* tK).comp (z1z:FX →+* FX[X]))
  ![(z1z:FX[X] →+* tK) (z7y:FX[X]),(z7y:tK)]
private theorem aOg (f :FX[X]) :
  C7 (C f)=F7 f := by
 have h: (oi.comp A7).comp (zhd znf) =
    F7:= by
  apply z86
  · intro a
    simp [F7,oi,A7,pZ]
  · simp [F7,oi,A7]
 simpa [C7,iJ,Gw,qQ.Ng] using
  zLs h f
private theorem epR:C7 (z7y:tK)=z9v 3:= by
 change ((z7y:tK).map (zhd znf)).eval₂
  (oi.comp A7) (z9v 3)= _
 rw [zSo,zC9]
private theorem cVM:azk=C7.comp ctH := by
 apply zXT
 · intro c
   simp [azk,ctH,aOg,F7]
 · intro i
   fin_cases i <;> simp [azk,ctH,aOg,epR,F7]
private theorem epD:zq4 azk :=
 zLm _ (by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction)
private abbrev aaw (I:znc z87) :=zNv (z87 ⧸ I)
private def azL (I:znc z87) :z87 →+* aaw I:= by
 let q:z87 →+* (z87 ⧸ I) :=zVv I
 let f : (z87 ⧸ I) →+* aaw I:=z12 _ _
 exact f.comp q
private theorem comap_ne_bot {I:znc z87} (hI:xN I) (hn : ¬ dual I) :
   I.comap C7 ≠ ⊥ := by
 intro hz
 have :I.IsPrime :=hI.prime
 let q:=azL I
 have hq:zq4 ((zVv I).comp azk) := by
   have hjet:zq4 ((zVv I).comp C7) := by
     apply (zli _).2
     simpa [← zEW,zlC] using hz
   rw [cVM,← zxS]
   refine hjet.comp ?_
   intro x y hxy
   apply epD
   rw [cVM]
   exact zPw C7 hxy
 have hj:zq4 (q.comp azk) :=
   (zxb (z87 ⧸ I) (aaw I)).comp hq
 let t:aQ →+* aaw I:=zIj hj
 let e :vR →+* aaw I :=
   zOD t ![q (z9v 0),q (z9v 1)]
 have hC (a :FX) :t (z12 FX aQ a)=q (znf a) := by
   rw [zG3 FX aZ aQ]
   simp [t,azk]
 have hX (i:Fin 2) :t (ek i)=q (z9v
     (zQY (by decide :2≤4) i+2)) := by
   simp [t,ek,azk]
 have he :e.comp CG=q:= by
   apply zXT
   · intro c
     simpa [e,CG] using hC c
   · intro i
     fin_cases i <;> simp [e,CG,hX]
 have :zAa aQ (Lj I) :=hI.jet_finite
 have hzero :zsE aQ (Lj I)=0:=Nat.eq_zero_of_not_pos hn
 have :zOt (Lj I) :=
   (Module.finrank_eq_zero_iff_of_free aQ (Lj I)).mp hzero
 have htop: (1 :vR)∈I.map CG :=
   Ideal.Quotient.eq_zero_iff_mem.mp (zJA _ _)
 have hle :I.map CG≤zdq e := by
   rw [zo0,zEW,he]
   intro x hx
   change q x=0
   simp [q,azL,Ideal.Quotient.eq_zero_iff_mem.mpr hx]
 have hbad:e 1=0:=RingHom.mem_ker.mp (hle htop)
 rw [zXs] at hbad
 exact (zOR : (1 :aaw I)≠0) hbad
attribute [local instance] Polynomial.algebra in
theorem cV2 {I:znc z87} (hI:xN I) (hn : ¬ dual I) :
   ∃ G:tK,G≠0∧I.comap C7=zye {G} := by
 let P:=I.comap C7
 have :I.IsPrime :=hI.prime
 have :P.IsPrime :=zG1 C7 I
 let F:=zNv (FX[X])
 let M:zdT tK:=(zgt (FX[X])).map (z1z:FX[X] →+* tK)
 have :=Polynomial.isLocalization (zgt (FX[X])) F
 have hdisj:z1v (M:Set tK) (P:Set tK) := by
   rw [zM4]
   rintro _ ⟨a,ha,rfl⟩ h
   change C7 (C a)∈I at h
   rw [aOg] at h
   have hq: ((zVv I).comp F7) a=0 :=
     Ideal.Quotient.eq_zero_iff_mem.mpr h
   exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
     (hI.ordinate_dominant (hq.trans (zhc _).symm))
 let Q:=P.map (z12 tK F[X])
 have :Q.IsPrime :=znL M F[X] P zWv hdisj
 have hle₀:=ztp (I:= Q)
 have hdim:zqe F[X]=1 := by simp [zZT]
 rw [hdim] at hle₀
 have hle :P.height≤1 := by
   rw [← IsLocalization.height_map_of_disjoint (S:=F[X]) M P hdisj]
   exact WithBot.coe_le_coe.mp hle₀
 have hp:P ≠ ⊥ := comap_ne_bot hI hn
 have hone :1≤P.height:= by
   simpa using zSK (bot_lt_iff_ne_bot.mpr hp)
 obtain ⟨G,hG⟩:=(UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
   (zWs hle hone)).principal
 refine ⟨G,?_,hG⟩
 intro hzero
 exact hp (by simpa [hzero] using hG)
end
end akR
end
section
namespace akR
noncomputable section
open gT pI Polynomial
open scoped BigOperators
private theorem dFp:abM (1 :tK) 0 0:= by
 refine ⟨zOR,by simp,?_⟩
 intro j i h
 by_cases hj:j=0
 · subst j
   by_cases hi:i=0
   · simp [hi]
   · simp [coeff_one,hi] at h
 · simp [coeff_one,hj] at h
private theorem bCk {F G:tK} {B J B' J' : ℕ}
   (hF:abM F B J) (hG:abM G B' J') :
   abM (F*G) (B+B') (J+J') := by
 classical
 refine ⟨zBS hF.1 hG.1,natDegree_mul_le_of_le hF.2.1 hG.2.1,?_⟩
 intro j i h
 by_contra! hdeg
 apply h
 rw [coeff_mul,finsetSum_coeff]
 apply zYF
 intro v hv
 rw [coeff_mul]
 apply zYF
 intro y hy
 have hv' := Finset.HasAntidiagonal.mem_antidiagonal.mp hv
 have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
 by_cases h1 : (F.coeff v.1).coeff y.1=0
 · rw [h1,zero_mul]
 by_cases h2 : (G.coeff v.2).coeff y.2=0
 · rw [h2,mul_zero]
 have hF' := hF.2.2 _ _ h1
 have hG' := hG.2.2 _ _ h2
 omega
theorem eOT {α:Type*} (S:zJe α) (g:α→tK) (b j:α→ℕ)
   (h : ∀ i∈S,abM (g i) (b i) (j i)) :
   abM (∏ i∈S,g i) (∑ i∈S,b i) (∑ i∈S,j i) := by
 classical
 induction S using zcw with
 | empty=>simpa using dFp
 | @insert a S ha ih =>
   rw [zqY ha,z5O ha,z5O ha]
   exact bCk (h _ (zT5 _ _))
     (ih fun i hi=>h i (zJN hi))
theorem eOY {α:Type*} {S:zJe α} {a :α} (ha :a∈S)
  (g:α→tK) {I:znc z87} (h:aaS (g a) I) :
  aaS (∏ i∈S,g i) I:= by
 obtain ⟨q,hq⟩:=Finset.dvd_prod_of_mem g ha
 change C7 (∏ i∈S,g i)∈I
 rw [hq,zok,zDE]
 exact I.mul_mem_left _ h
end
end akR
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace akR
noncomputable section
open gT pI Polynomial
open scoped BigOperators
def c1 :Prop :=
  ∀ (I:znc z87) (G:tK),xN I→G≠0 →
    I.comap C7=zye {G} →
    zq4 (apn I)
def c2 :Prop :=
  ∀ (I:znc z87) (G:tK),
    I.comap C7=zye {G} → zq4 (apn I) →
    (∃ f : (dV[X] ⧸ zye {bJ2 G}) →ₗ[dV]
      ani I,zq4 f) ∧
    (∃ f : (dV[X] ⧸ zye {bJh G}) →ₗ[dV]
      Ik I,zq4 f)
private theorem c3F (h1 :c1) (h2 :c2) {I:znc z87}
  (hI:xN I) (hn : ¬ dual I) :
  ∃ G:tK,abM G (pN I 2) (pN I 1)∧aaS G I:= by
 obtain ⟨G,hG,hi⟩:=cV2 hI hn
 obtain ⟨⟨f,hf⟩,⟨g,hg⟩⟩:=h2 I G hi (h1 I G hI hG hi)
 have :=hI.a6j
 have :=hI.bfE
 have ho:=zdv (f :=f) hf
 have hm:=zdv (f :=g) hg
 rw [z35,eHR] at ho
 rw [z35] at hm
 refine ⟨G,⟨hG,ho,fun j i h=>(eAJ hG h).trans hm⟩,?_⟩
 change G∈I.comap C7
 rw [hi]
 exact zCn rfl
end
end akR
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace bzS
noncomputable section
open cu gT pI akR Polynomial
private abbrev AH :aZ →+* Ambient:=oi.comp pZ
private theorem co5 {I:znc z87} (hI:xN I) :
   zq4 ((zVv I).comp AH) := by
 let q:=(zVv (I.map Dk)).comp Dk
 let e :aQ →+* Y0 I:=z12 aQ (Y0 I)
 have he :q.comp AH=e.comp (z12 aZ aQ) := by
   apply zXT
   · intro c
     simp only [zQb]
     rw [← zKm,← zG3 FX aZ aQ]
     simp [q,oi,pZ,Dk]
     rfl
   · intro i
     fin_cases i <;> simp [q,AH,oi,pZ,Dk,e,ek] <;> rfl
 let:zue (Y0 I) :=Module.nontrivial_of_finrank_pos hI.seed_size.1
 apply (zLn ((zVv I).comp AH)).2
 intro f hf
 have hmem:AH f∈I:=Ideal.Quotient.eq_zero_iff_mem.mp hf
 have hz :q (AH f)=0 :=
   Ideal.Quotient.eq_zero_iff_mem.mpr (z7X Dk hmem)
 have hzero : (e.comp (z12 aZ aQ)) f=0:= by
   rw [← he]
   exact hz
 have hinj:zq4 (e.comp (z12 aZ aQ)) :=
   e.injective.comp (zxb aZ aQ)
 exact hinj (hzero.trans (zhc (e.comp (z12 aZ aQ))).symm)
private theorem aOg (f :FX[X]) :
  C7 (C f)=F7 f := by
 have h: (oi.comp A7).comp (zhd znf) =
    F7:= by
  apply z86
  · intro a
    simp [F7,oi,A7,pZ]
  · simp [F7,oi,A7]
 simpa [C7,iJ,Gw,qQ.Ng] using
  zLs h f
private instance gQd (I:znc z87) [I.IsPrime] :
   (I.comap C7).IsPrime :=
 (zWv :I.IsPrime).comap C7
private abbrev tJ (I:znc z87) :=zNv (aRM I)
private abbrev aaw (I:znc z87) :=zNv (gk I)
private def JH (I:znc z87) :tK →+* tJ I :=
 (z12 (aRM I) (tJ I)).comp (zVv _)
private def azL (I:znc z87) :z87 →+* aaw I :=
 (z12 (gk I) (aaw I)).comp (zVv I)
private def aVr (I:znc z87) [I.IsPrime] :tJ I →+* aaw I :=
 zIj (K:=tJ I)
  (g:=(z12 (gk I) (aaw I)).comp
    (z3G I C7 zs1))
  ((zxb (gk I) (aaw I)).comp
    Ideal.quotientMap_injective)
private theorem cV0 (I:znc z87) [I.IsPrime] (f :tK) :
  aVr I (JH I f)=azL I (C7 f) := by
 simp [aVr,JH,azL,z5h]
private theorem bJ4 {I:znc z87} [I.IsPrime] (hI:xN I) :
  zq4 ((JH I).comp (C:FX[X] →+* tK)) := by
 intro f g h
 apply hI.ordinate_dominant
 have h' := zPw (aVr I) h
 simp only [zQb,cV0,aOg,azL] at h'
 exact zxb (gk I) (aaw I) h'
private theorem eqd {I:znc z87} [I.IsPrime] (hI:xN I)
   {G:tK} (hG:G≠0) (hGI:G∈I.comap C7) :
   zls FX (tJ I)=1 := by
 let:znE (FX[X]) (tJ I) :=
   (zSO _ _).mpr (bJ4 hI)
 let v :=JH I (z7y:tK)
 have hπ: (zEU v :tK →ₐ[FX[X]] tJ I).toRingHom=JH I:= by
   apply z86
   · intro a
     change zEU v (C a)= _
     rw [z8q]
     rfl
   · change zEU v (z7y:tK)=JH I (z7y:tK)
     exact zw0 v
 have hv :zxf (FX[X]) v := by
   refine ⟨G,hG,?_⟩
   change (zEU v :tK →ₐ[FX[X]] tJ I).toRingHom G=0
   rw [hπ]
   change z12 (aRM I) (tJ I) (zVv _ G)=0
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr hGI,zhc]
 have hpoly (f :tK) :zxf (FX[X]) (JH I f) := by
   rw [← hπ]
   exact (Algebra.isAlgebraic_adjoin_singleton_iff.mpr hv) _
     (Polynomial.aeval_mem_adjoin_singleton _ _)
 let:zjH (FX[X]) (tJ I) := by
   constructor
   intro z
   obtain ⟨f,g,-,rfl⟩:=zJC (aRM I) z
   obtain ⟨f,rfl⟩:=zld f
   obtain ⟨g,rfl⟩:=zld g
   rw [div_eq_mul_inv]
   exact (hpoly f).mul (hpoly g).inv
 rw [← z5k FX (FX[X]),
   zBA,zBT (R:=FX[X]),z0a]
private theorem epv (I:znc z87) [I.IsPrime] (a :FX) :
  aVr I (z12 FX (tJ I) a)=azL I (znf a) := by
 change aVr I (JH I (C (C a)))= _
 rw [cV0,aOg]
 simp [F7]
private theorem eFu {k M E :Type} [zrb k] [zrb M] [zrb E]
   [zZE k M] [zZE M E] (hM:zls k M=1) (x y :E)
   (hseed :zq4
     (zOD ((z12 M E).comp (z12 k M)) (![x,y] :Fin 2→E))) :
   ¬ (zxf M x∧zxf M y) := by
 intro h
 let F:=algebraicClosure M E
 let:zZE k F:=((z12 M F).comp (z12 k M)).toAlgebra
 let:zsf k M F:=zsL fun _=>rfl
 let t:Fin 2→F :=
   ![⟨x,mem_algebraicClosure_iff.mpr h.1⟩,⟨y,mem_algebraicClosure_iff.mpr h.2⟩]
 let f :z3y (Fin 2) k →ₐ[k] F:=zIe t
 have he :F.subtype.comp f.toRingHom =
     zOD ((z12 M E).comp (z12 k M)) ![x,y] := by
   apply zXT
   · intro a
     change F.subtype (zIe t (znf a))= _
     rw [zXr,zTv,zQb]
     rfl
   · intro i
     change F.subtype (zIe t (z9v i))= _
     rw [zTw,zrD]
     fin_cases i <;> rfl
 have hinj:zq4 f := by
   intro p q hpq
   apply hseed
   rw [← he]
   exact zPw F.subtype hpq
 have htr :=trdeg_le_of_injective f hinj
 rw [← z5k k M (A:=F),hM,zBT (R:=M),z0a,
   zUx] at htr
 have hbad: (2 :zpf.{0})≤1 := by
   simpa only [Cardinal.lift_id,zUc,Nat.cast_ofNat] using htr
 have hn: (2 :ℕ)≤1 := by exact_mod_cast hbad
 omega
theorem proof :akR.c1 := by
  intro I G hI hG he
  let:I.IsPrime :=hI.prime
  let:zZE (tJ I) (aaw I) :=(aVr I).toAlgebra
  let:Infinite (tJ I) :=ztd _ (bJ4 hI)
  have hGI:G∈I.comap C7:= by
    rw [he]
    exact zCn rfl
  let x :=azL I (z9v 0)
  let y :=azL I (z9v 1)
  let m:aRM I →+* tJ I:=z12 _ _
  let n:gk I →+* aaw I:=z12 _ _
  have hcomp: (zDK n).comp (apn I) =
      (aN1 (M:=tJ I) x y).comp (zDK m) := by
    apply zXT
    · intro b
      simp [apn,aN1,m,n,aVr,RingHom.algebraMap_toAlgebra]
    · intro i
      fin_cases i <;> simp [apn,aN1,x,y,n,azL]
  have hseed :zOD
      ((z12 (tJ I) (aaw I)).comp (z12 FX (tJ I)))
        (![x,y] :Fin 2→aaw I)=(azL I).comp AH := by
    apply zXT
    · intro a
      simp only [zTv,zQb]
      change aVr I (z12 FX (tJ I) a) =
        azL I (AH (znf a))
      rw [epv]
      simp [AH,oi,pZ]
    · intro i
      fin_cases i <;> simp [x,y,AH,oi,pZ]
  have hseed_inj:zq4 (zOD
      ((z12 (tJ I) (aaw I)).comp (z12 FX (tJ I)))
        (![x,y] :Fin 2→aaw I)) := by
    rw [hseed]
    exact (zxb (gk I) (aaw I)).comp (co5 hI)
  have ht : ¬ (zxf (tJ I) x∧zxf (tJ I) y) :=
    eFu (k :=FX) (M:=tJ I) (E :=aaw I)
      (eqd hI hG hGI) x y hseed_inj
  have hinj:zq4 ((zDK n).comp (apn I)) := by
    rw [hcomp]
    exact (efz (M:=tJ I) (E :=aaw I) x y ht).comp
      (zNV m (zxb (aRM I) (tJ I)))
  intro p q hpq
  apply hinj
  exact zPw (zDK n) hpq
end
end bzS
end
section
namespace akQ
noncomputable section
open cu gT pI
abbrev lK (F:Type) [zrb F] :=z3y (Fin 2) F
abbrev Zj {F:Type} [zrb F] (φ:z87 →+* lK F) (I:znc z87) :=
 lK F ⧸ I.map φ
abbrev a07 (P Q:Jet) :znc Ambient:=zye {iJ P,iJ Q}
abbrev aBX {F:Type} [zrb F] (f g:lK F) :=
 lK F ⧸ zye {f,g}
def Fp (kK:Bool) :Fin 4→lK dV :=
  ![znf (kz 2)-MvPolynomial.C (kz 0)*z9v 0,
    z9v 0,
    if kK then
     znf (kz 3)-MvPolynomial.C (kz 1)*z9v 1
    else znf (kz 3),
    z9v 1]
def lineMap (kK:Bool) :z87 →+* lK dV :=
 zOD (MvPolynomial.C.comp (z12 FX dV)) (Fp kK)
structure aSD (F:Type) [zrb F] (φ:z87 →+* lK F) (k :Fin 4) :Prop where
 flat :letI:=φ.toAlgebra; Module.Flat z87 (lK F)
 finite_rank : ∀ I:znc z87,xN I →
  zAa F (Zj φ I) ∧
    zsE F (Zj φ I)=pN I k
 prime_over : ∀ I:znc z87,I.IsPrime→ I.map φ ≠ ⊤ →
  (I.map φ).IsPrime∧(I.map φ).comap φ=I
 relPrime : ∀ a b:z87,IsRelPrime a b→ IsRelPrime (φ a) (φ b)
end
end akQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace aqb
open cu gT pI Polynomial
noncomputable def Co:zS3 →+* Ambient:=iJ.comp C
@[simp] theorem btc (f :zS3) :
   Co f=iJ (C f) :=rfl
abbrev aBW (I:znc z87) [I.IsPrime] :=zhz I
noncomputable abbrev aIW (I:znc z87) [I.IsPrime] :
 z87 →+* aBW I:=z12 z87 (aBW I)
noncomputable def azl (I:znc z87) :znc Ambient :=
 (I.comap C7).map C7
noncomputable abbrev aRO (I:znc z87) [I.IsPrime] :=
 let R:=aBW I
 letI:za6 R:=inferInstanceAs (za6 (zhz I))
 let J:znc R:=(azl I).map (aIW I)
 R ⧸ (J:Submodule R R)
noncomputable abbrev brm (I:znc z87) [I.IsPrime] :
 aBW I →+* aRO I:=zVv _
end aqb
end
