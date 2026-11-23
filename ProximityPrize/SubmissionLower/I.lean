import ProximityPrize.SubmissionLower.V
import ProximityPrize.SubmissionLower.Z3EWiUc
import ProximityPrize.SubmissionLower.ZFFuWqa
import ProximityPrize.SubmissionLower.ZGlW6Oc
import ProximityPrize.SubmissionLower.ZgdIx1d
set_option Elab.async false
open _root_ renaming AlgHom.coe_ringHom_injective → zst, AlgHom.commutes → zKk, AlgHom.comp_apply → zip, AlgHom.ext → zjT, AlgHom.id → zhD, AlgHom.liftEquiv → zuh, Algebra → zZE, Algebra.EssFiniteType → zl5, Algebra.EssFiniteType.comp → zQi, Algebra.EssFiniteType.of_comp → z9q, Algebra.EssFiniteType.of_isLocalization → zrU, Algebra.IsAlgebraic → zjH, Algebra.IsIntegral.isIntegral → zmn, Algebra.TensorProduct.includeRight → zgi, Algebra.TensorProduct.map → zv2, Algebra.TensorProduct.tensorQuotientEquiv → zTd, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul → zTe, Algebra.algebraMap_self → zCp, Algebra.finite_of_essFiniteType_of_isAlgebraic → zNf, Algebra.ofId → zNX, Algebra.smul_def → zd5, CommRing → za6, DFunLike.congr_fun → zmU, Field → zrb, Fin.cons → z4W, Fin.cons_succ → zVG, Fin.cons_zero → zhe, Fin.sum_univ_eq_sum_range → zdx, Fin.sum_univ_succ → zCS, Fin.val_injective → z0e, Finset.mul_sum → zxw, Finset.prod_congr → zX3, Finset.prod_mul_distrib → zeY, Finset.prod_pow_eq_pow_sum → zX0, Finset.range → z4x, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Finset.sum_eq_zero → zYF, Finset.sum_mul → zkq, Finset.sup_mono → zRS, Finsupp.add_apply → zSs, Finsupp.basisSingleOne → zXB, Finsupp.coe_basisSingleOne → zwk, Finsupp.degree_apply → zqc, Finsupp.degree_eq_sum → zFi, Finsupp.degree_eq_weight_one → zKx, Finsupp.linearCombination → zzF, Finsupp.linearCombination_apply → z0S
open _root_ renaming Finsupp.prod → zsa, Finsupp.single → zhf, Finsupp.weight_single_one_apply → z7P, Fintype → z85, Fintype.card_fin → zgY, Fintype.sum_prod_type → zsI, Function.Injective → zq4, Function.Surjective → zpX, Function.comp_apply → z3s, Ideal → znc, Ideal.Quotient.algHom_ext → zoA, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.factor_surjective → zuo, Ideal.Quotient.factorₐ → z5F, Ideal.Quotient.isDomain_iff_prime → zMn, Ideal.Quotient.lift → zP2, Ideal.Quotient.lift_mk → z0R, Ideal.Quotient.liftₐ → zTA, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.eq_top_iff_one → zhc, Ideal.eq_top_of_isUnit_mem → zAn, Ideal.exists_le_maximal → zsl, Ideal.homogeneous_span → zqZ, Ideal.kerLiftAlg → zdc, Ideal.kerLiftAlg_injective → zvo, Ideal.map_map → z0L, Ideal.map_span → zlN, Ideal.map_sup → zXe, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.quotientEquivAlg → zpY, Ideal.quotientEquivAlgOfEq → z9k, Ideal.quotientEquivAlgOfEq_mk → zeu, Ideal.quotientMapₐ → zwL, Ideal.span → zye, Ideal.span_singleton_pow → zNi, Ideal.subset_span → zCn, Ideal.zero_mem → znl, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.comap_isAlgebraic_iff → zE4, IsFractionRing.div_surjective → zJC, IsFractionRing.injective → zxb, IsFractionRing.lift → zIj
open _root_ renaming IsFractionRing.liftAlgHom → zeU, IsFractionRing.lift_algebraMap → zoc, IsFractionRing.map → zJ1, IsFractionRing.ringHom_ext → z2O, IsLocalization.Away → zSp, IsLocalization.Away.liftAlgHom → zHH, IsLocalization.Away.lift_eq → zaz, IsLocalization.Away.tensorProductEquivTMulRight → zaF, IsLocalization.injective → zHp, IsLocalization.lift → zvq, IsLocalization.lift_eq → zX4, IsLocalization.map_eq → zi7, IsLocalization.map_units → z0j, IsLocalization.ringHom_ext → zuW, IsLocalization.tensorProductEquivOfMapIncludeRight_tmul → zL5, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.algebraMap_eq → zYY, IsScalarTower.of_algHom → zKB, IsScalarTower.of_algebraMap_eq → zsL, IsScalarTower.toAlgHom → zE2, LinearIndependent → z14, LinearMap.ker → z83, LinearMap.mulLeft → zzN, Module → zeq, Module.Basis → z39, Module.Basis.coord_apply → zVi, Module.Basis.ofVectorSpace → zz1, Module.Finite → zAa, Module.Finite.equiv → zZc, Module.Finite.of_surjective → zIV, Module.compHom → zki, Module.finrank → zsE, Module.finrank_mul_finrank → zS7, Module.finrank_zero_of_subsingleton → zuF, Module.rank → z1x, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aeval_X → zTw, MvPolynomial.affineHilbertPolynomial → zIU, MvPolynomial.algHom_ext → zpH, MvPolynomial.algebraMap_def → zu8, MvPolynomial.algebraTensorAlgEquiv → zoR, MvPolynomial.comp_aeval_apply → zrc, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD
open _root_ renaming MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.eval₂_comp → z6r, MvPolynomial.finSuccEquiv → z8s, MvPolynomial.funext → zjN, MvPolynomial.homogeneousSubmodule → zbm, MvPolynomial.induction_on → z5i, MvPolynomial.map → zDK, MvPolynomial.mapAlgHom → zWY, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.map_injective → zNV, MvPolynomial.map_map → z6Y, MvPolynomial.mem_support_iff → zuk, MvPolynomial.ringHom_ext → zXT, MvPolynomial.trdeg_of_isDomain → zUx, MvPolynomial.uniqueAlgEquiv → zpe, Nat.add_comm → zg2, Nat.card_fin → zJa, Nat.cast_add → z6H, Nat.cast_one → z4o, Nat.choose_zero_right → zCM, Nat.eq_zero_of_le_zero → za7, Nat.le_of_lt_succ → zeh, Nat.le_succ → zqk, Nat.lt_succ_of_le → zB1, Nat.sub_add_cancel → zxt, Nat.zero_le → zD0, Polynomial → zM1, Polynomial.C → z1z, Polynomial.CAlgHom → z97, Polynomial.C_mul_X_pow_eq_monomial → zoT, Polynomial.X → z7y, Polynomial.X_ne_zero → z05, Polynomial.X_pow_mul_C → zxl, Polynomial.aeval → zEU, Polynomial.aeval_C → z8q, Polynomial.aeval_X → zw0, Polynomial.algebraMap_apply → zpj, Polynomial.algebraMap_eq → zrE, Polynomial.backwardDifference → zW9, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.coe_mapRingHom → zKC, Polynomial.coeff_X_pow_mul → zxk, Polynomial.coeff_eq_zero_of_natDegree_lt → zQl, Polynomial.coeff_map → z0b, Polynomial.coeff_monomial → zQm, Polynomial.coeff_monomial_same → z2j
open _root_ renaming Polynomial.coeff_zero → zO6, Polynomial.coeff_zero_eq_eval_zero → zTt, Polynomial.commSemiring → zEw, Polynomial.evalRingHom → zhy, Polynomial.eval_C → zFf, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_C → zJU, Polynomial.eval₂_X → zC9, Polynomial.eval₂_map → zem, Polynomial.eval₂_monomial → zFK, Polynomial.eval₂_mul → zxy, Polynomial.finsetSum_coeff → zaW, Polynomial.hasseDeriv → z75, Polynomial.hom_eval₂ → zly, Polynomial.induction_on' → zCU, Polynomial.leadingCoeff → z4w, Polynomial.mapAlgHom → z0c, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.map_id → zei, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, Polynomial.monic_prod_of_monic → zRn, Polynomial.monomial → zdM, Polynomial.monomial_mul_monomial → zva, Polynomial.monomial_pow → zCL, Polynomial.monomial_zero_right → zQQ, Polynomial.natDegree_C → zti, Polynomial.ofFn → zDW, Polynomial.ofFn_coeff_eq_val_of_lt → zPX, Polynomial.ringHom_ext → z86, Polynomial.toMvPolynomial → z3n, RingHom.Finite.comp → zfr, RingHom.Finite.of_surjective → zO7, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.ext → zz4, RingHom.id → zz5, RingHom.injective_iff_ker_eq_bot → zli, RingHom.ker → zdq, RingHom.kerLift_injective → zuJ, RingHom.ker_eq_bot_iff_eq_zero → zr7, RingHom.ker_isPrime → zgL, Set.image_singleton → zyk, Set.mem_range_self → zWL, Set.mem_singleton → zT1
open _root_ renaming Set.mem_union_left → zt3, Set.range → zxp, Submodule.Quotient.mk_eq_zero → ziM, Submodule.comapSubtypeEquivOfLe → zTz, Submodule.sub_mem_iff_left → zSM, Submonoid.powers → zSL, Subsingleton → zOt, TensorProduct.equivFinsuppOfBasisLeft → znu, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply → zy4, TensorProduct.inductionOn → z2P, TensorProduct.mk → zUP
set_option autoImplicit true
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace B7
noncomputable section
open K1 aR oR Finset MvPolynomial
open scoped BigOperators Polynomial
private theorem b9N {w Γ s d}
   (hcap : ∀ i:I,(∃ γ∈Γ,(s γ).eval (node i)≠w i) →
     (Γ.filter fun γ=>(s γ).eval (node i)=w i).card≤d) :
   ang w Γ s d:= by
 classical
 let persistent:=univ.filter fun i:I => ∀ γ∈Γ,(s γ).eval (node i)=w i
 refine ⟨persistent,?_,?_⟩
 · exact fun i hi=>(mem_filter.mp hi).2
 · intro i hi
   apply hcap i
   by_contra! hall
   exact hi (mem_filter.mpr ⟨mem_univ _,hall⟩)
end
end B7
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace B7
noncomputable section
open K1 aR oR Finset MvPolynomial
open scoped BigOperators Polynomial
private theorem bqq (f :af 3) : (GZ f).totalDegree≤f.totalDegree := by
 unfold GZ MvPolynomial.totalDegree
 exact zRS (support_map_subset (algebraMap ao[X] dF) f)
end
end B7
end
section
namespace Ey
noncomputable section
open aR B7 MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
section ScalarExtension
variable {F E σ:Type*} [zrb F] [zrb E] [zZE F E]
private def Pd (I:znc (z3y σ F)) :
   E ⊗[F] (z3y σ F ⧸ I) ≃ₐ[E]
     z3y σ E ⧸ I.map (zDK (algebraMap F E)) := by
 let e :=zoR (σ:=σ) F E
 let ι:z3y σ F →ₐ[F] E ⊗[F] z3y σ F:=zgi
 have hcomp:e.toRingHom.comp ι.toRingHom=zDK (algebraMap F E) := by
   apply zz4
   intro p
   change e (1 ⊗ₜ[F] p)= _
   simp [e]
 refine (zTd (R:=F) E _ E I).trans
   (zpY _ _ e ?_)
 exact ((z0L (I:=I) ι.toRingHom e.toRingHom).trans
   (congrArg (fun f=>I.map f) hcomp)).symm
private theorem eQw (I:znc (z3y σ F)) (p:z3y σ F) :
  Pd (E :=E) I (1 ⊗ₜ[F] (zVv I p)) =
   zVv _ (zDK (algebraMap F E) p) := by
 simp [Pd]
theorem emY (I:znc (z3y σ F)) (n:ℕ) :
   affineHilbertFunction (I.map (zDK (algebraMap F E))) n =
     affineHilbertFunction I n:= by
 let e :=(Pd (E :=E) I).toLinearEquiv
 let V:=quotientDegreeLE I n
 have h: (V.baseChange E).map e.toLinearMap =
     quotientDegreeLE (I.map (zDK (algebraMap F E))) n:= by
   dsimp only [V,quotientDegreeLE,restrictTotalDegree]
   simp only [restrictSupport_eq_span,Submodule.map_span,Submodule.baseChange_span,
     Set.image_image]
   congr 1
   apply Set.image_congr
   intro m hm
   change Pd (E :=E) I (1 ⊗ₜ[F] (zVv I (monomial m 1))) =
     zVv _ (monomial m 1)
   rw [eQw,MvPolynomial.map_monomial,map_one]
 rw [affineHilbertFunction,← h,
   ← (Submodule.equivMapOfInjective e.toLinearMap e.injective (V.baseChange E)).finrank_eq,
   ← (Submodule.toBaseChange.toLinearEquiv E V).finrank_eq,Module.finrank_baseChange]
 rfl
theorem ZI [Finite σ] (I:znc (z3y σ F)) :
   affineHilbertPolynomial (I.map (zDK (algebraMap F E))) =
     affineHilbertPolynomial I:= by
 obtain ⟨n,hn⟩:=exists_eval_affineHilbertPolynomial I
 symm
 apply eq_affineHilbertPolynomial_of_eval_eq (N₀:=n)
 intro m hm
 rw [emY]
 exact hn m hm
end ScalarExtension
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem bqp (P:znc jo) (hP:P.IsPrime) : (oV P).IsPrime := by
  let R:=z3y rS ao[X]
  let e :R ≃ₐ[ao] jo[X] :=
    (optionEquivRight ao rS).symm.trans (optionEquivLeft ao rS)
  let P' : znc R:=P.map (zDK (z1z:ao →+* ao[X]))
  have heC:e.toRingHom.comp (zDK (z1z:ao →+* ao[X])) =
      (z1z:jo →+* jo[X]) := by
    apply zXT
    · intro a
      change e (zDK z1z (znf a))= _
      rw [zpw]
      change optionEquivLeft ao rS
        ((optionEquivRight ao rS).symm (znf (z1z a)))= _
      rw [← optionEquivRight_C,AlgEquiv.symm_apply_apply,optionEquivLeft_C]
    · intro a
      change e (zDK z1z (z9v a))= _
      rw [z7N]
      change optionEquivLeft ao rS
        ((optionEquivRight ao rS).symm (z9v a))= _
      rw [← optionEquivRight_X_some,AlgEquiv.symm_apply_apply,optionEquivLeft_X_some]
  have heP:P'.map e.toRingHom=P.map (z1z:jo →+* jo[X]) := by
    rw [show P' = P.map _ from rfl,z0L,heC]
  have hP' : P'.IsPrime := by
    have hmap :=(Ideal.isPrime_map_C_iff_isPrime P).2 hP
    rw [← heP] at hmap
    have :=hmap
    rw [← Ideal.comap_map_of_bijective (I:=P') e.toRingHom e.bijective]
    exact Ideal.comap_isPrime e.toRingHom _
  let M:Submonoid R:=(nonZeroDivisors ao[X]).map (znf (σ:=rS))
  have hdisj:Disjoint (M:Set R) (P' : Set R) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s,hs,rfl⟩ hp
    have hmem:=z7X e.toRingHom hp
    rw [heP,Ideal.mem_map_C_iff] at hmem
    have heS:e.toRingHom (znf s) =
        Polynomial.map (znf:ao →+* jo) s := by
      have he' : e.toRingHom.comp (znf:ao[X] →+* R) =
          zhd (znf:ao →+* jo) := by
        apply z86
        · intro a
          change e (znf (z1z a))= _
          change optionEquivLeft ao rS
            ((optionEquivRight ao rS).symm (znf (z1z a)))= _
          rw [← optionEquivRight_C,AlgEquiv.symm_apply_apply,optionEquivLeft_C]
          simp
        · change e (znf z7y)= _
          change optionEquivLeft ao rS
            ((optionEquivRight ao rS).symm (znf z7y))= _
          rw [← optionEquivRight_X_none,AlgEquiv.symm_apply_apply,optionEquivLeft_X_none]
          simp
      exact zmU he' s
    have hi:s.leadingCoeff≠0:=Polynomial.leadingCoeff_ne_zero.mpr (nonZeroDivisors.ne_zero hs)
    have hconst:=hmem s.natDegree
    rw [heS,z0b] at hconst
    exact hP.ne_top (zAn _ hconst (IsUnit.map _ (isUnit_iff_ne_zero.mpr hi)))
  have hprime :=IsLocalization.isPrime_of_isPrime_disjoint M mK P' hP' hdisj
  have hext:P'.map (algebraMap R mK)=oV P:= by
    change (P.map _).map (zDK (algebraMap ao[X] dF))= _
    rw [z0L]
    congr 1
    apply zXT
    · intro c
      simp only [zQb,zpw]
      rfl
    · simp
  exact hext ▸ hprime
private theorem dXb {F σ τ:Type*} [zrb F] [Finite σ] [Finite τ]
  {I:znc (z3y σ F)} {J:znc (z3y τ F)}
  {s :z3y σ F} {t:z3y τ F}
  (φ: (z3y σ F ⧸ I) →ₐ[F] (z3y τ F ⧸ J))
  (ht:φ (zVv I s)=zVv J t)
  (hreg:IsLeftRegular (zVv J t))
  (hrec : ∀ x,∃ q m,φ q=φ (zVv I s)^m*x) :
  (affineHilbertPolynomial J).natDegree≤(affineHilbertPolynomial I).natDegree := by
 let a :=zVv I s
 let A:=Localization.Away a
 let B:=Localization.Away (zVv J t)
 have :zSp (φ a) B:= by
  change zSp (φ (zVv I s)) B
  rw [ht]
  infer_instance
 let ψ:A →ₐ[F] B:=IsLocalization.Away.mapₐ (R:=F) A B φ a
 have hψ:zpX ψ :=
  (IsLocalization.Away.map_surjective_iff A B φ.toRingHom a).2 hrec
 exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg ψ hψ
theorem aTz (P:znc jo) (g d:nW) (h:XP P g d) :
    (affineHilbertPolynomial P).natDegree=2 := by
  let J:znc nW:=zye {g}
  let A:=nW ⧸ J
  let B:=mK ⧸ oV P
  let φ:A →ₐ[dF] B:=zwL _ tO h.image.ge
  have hφ:zq4 φ:=Ideal.quotientMap_injective' (H :=h.image.ge) h.image.le
  let a :A:=zVv J d
  let b:B:=φ a
  have hneq :zVv (oV P) (tO d)≠0:= by
    rw [Ne,z1Q]
    exact fun hd=>h.regular_open (h.image ▸ hd)
  have :=bqp P h.prime
  have hb:IsLeftRegular (zVv (oV P) (tO d)) :=
    (IsRegular.of_ne_zero hneq).1
  have hrecover (f :mK) : ∃ q:A,∃ m:ℕ,
      φ q=b^m* zVv (oV P) f := by
    induction f using z5i with
    | C c =>
      refine ⟨algebraMap dF A c,0,?_⟩
      simpa only [zKk,pow_zero,one_mul] using
        (show algebraMap dF B c=zVv (oV P) (znf c) from rfl)
    | add f r hf hr =>
      obtain ⟨u,m,hu⟩:=hf
      obtain ⟨v,n,hv⟩:=hr
      refine ⟨a^n*u+a^m*v,m+n,?_⟩
      simp only [map_add,map_mul,map_pow,hu,hv,← show b=φ a from rfl,pow_add]
      ring
    | mul_X f i hf =>
      obtain ⟨u,m,hu⟩:=hf
      obtain ⟨v,n,hv⟩:=h.recover i
      have hv' : φ (zVv J v) =
          b^n* zVv (oV P) (z9v i) := by
        have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr hv
        simp only [map_sub,map_mul,map_pow,sub_eq_zero] at hz
        exact hz.symm
      refine ⟨u* zVv J v,m+n,?_⟩
      simp only [map_mul,hu,hv',pow_add]
      ring
  have hle :=natDegree_affineHilbertPolynomial_le_of_injective φ hφ
  have hge : (affineHilbertPolynomial (oV P)).natDegree≤(affineHilbertPolynomial J).natDegree := by
    apply dXb (s :=d) (t:=tO d) φ rfl hb
    intro x
    obtain ⟨f,rfl⟩:=zld x
    exact hrecover f
  have hJ: (affineHilbertPolynomial J).natDegree=2 := by
    have hproper :J ≠ ⊤ := by
      intro htop
      apply h.regular_open
      change d∈J
      simp [htop]
    have heq :=natDegree_affineHilbertPolynomial_span_singleton_add_one h.equation_ne hproper
    rw [Nat.card_eq_fintype_card,zgY] at heq
    change (affineHilbertPolynomial J).natDegree+1=3 at heq
    omega
  rw [← ZI (E :=dF) P]
  exact (le_antisymm hge hle).trans hJ
end
end Ey
end
section
namespace XW
noncomputable section
open cu gT DQ Cu MvPolynomial
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g n:ℕ)
    (R:wJ C₀ J g) (A:yI R n),
    (affineHilbertPolynomial (TU A)).natDegree≤1 →
    atV (Gu (jY n) (TU A)) (a2G n) ∧
      atV (Gu aQ (TU A)) (aIM A.equation)
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g n:ℕ)
    (R:wJ C₀ J g) (A:yI R n),
    zAa (jY n) (aYv A) →
    zAa (jY n) (aAM (EF A)) ∧
      zsE (jY n) (aAM (EF A)) ≤
        gY A*zsE (jY n) (aYv A)
def c3:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g n:ℕ)
    (R:wJ C₀ J g) (A:yI R n),
    0<g→zAa aQ (SI J) →
    zAa aQ (anh A) →
    gY A*zsE aQ (anh A) ≤
      zsE aQ (SI J)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :Cu.c3:= by
 intro C₀ _ J g H n R A hg hroot hH
 obtain ⟨hdBase,hdCoeff⟩:=aTz A
 obtain ⟨hparam,hord⟩:=h1 C₀ J g n R A hdCoeff
 have hp:affineHilbertPolynomial (Gu (jY n) (TU A)) =
     affineHilbertPolynomial (TU A) :=
   Ey.ZI _
 have hy :affineHilbertPolynomial (Gu aQ (TU A)) =
     affineHilbertPolynomial (TU A) :=
   Ey.ZI _
 have hpdim: (affineHilbertPolynomial (Gu (jY n) (TU A))).natDegree
     ≤ 1 := by rwa [hp]
 have hydim: (affineHilbertPolynomial (Gu aQ (TU A))).natDegree
     ≤ 1 := by rwa [hy]
 obtain ⟨hpf,hplen⟩:=cXt hpdim hparam
 obtain ⟨hyf,hylen⟩:=cXt hydim hord
 have hlen:zsE (jY n) (aYv A) =
     zsE aQ (anh A) := by
   rw [hp] at hplen
   rw [hy] at hylen
   exact_mod_cast hplen.trans hylen.symm
 obtain ⟨hfin,hbudget⟩:=h2 C₀ J g n R A hpf
 refine ⟨hdBase,hfin,hbudget.trans ?_⟩
 rw [hlen]
 exact (h3 C₀ J g n R A hg hroot hyf).trans hH
end
end XW
end
section
set_option maxHeartbeats 600000
namespace aFZ
noncomputable section
section OffsetLocalization
set_option linter.unusedSectionVars false
open MvPolynomial
open scoped nonZeroDivisors
abbrev aje (k :Type*) [za6 k] (n:ℕ) :=
 z3y (Option (Fin n)) k
variable {k σ S:Type*} [za6 k] {n:ℕ}
variable [za6 S] [zZE k S] [zZE (aje k n) S]
variable [zsf k (aje k n) S] [z0o (aje k n) S]
abbrev ax2 (I:znc (z3y σ k)) :=
 z3y (Fin n) (z3y σ k ⧸ I)
def bPX (I:znc (z3y σ k)) (j:Fin n→σ) :
    ax2 (n:=n) I :=
  ∑ i,z9v i*C (zVv I (z9v (j i)))
def substitute (I:znc (z3y σ k)) (j:Fin n→σ) :
    aje k n →+* ax2 (n:=n) I :=
  eval₂Hom (C.comp ((zVv I).comp C)) (fun i =>
    i.elim (bPX I j) z9v)
abbrev aXX (I:znc (z3y σ k)) (j:Fin n→σ) :
   Submonoid (ax2 (n:=n) I) :=
 (aje k n)⁰ |>.map (substitute I j).toMonoidHom
abbrev aiQ (I:znc (z3y σ k)) (j:Fin n→σ) :=
 Localization (M:=ax2 (n:=n) I) (aXX I j)
instance gQz (I:znc (z3y σ k)) (j:Fin n→σ) :
   za6 (aiQ I j) :=
 @OreLocalization.instCommRing (ax2 (n:=n) I) inferInstance
   (aXX I j) inferInstance
private def exn (I:znc (z3y σ k)) (j:Fin n→σ) :
  S →+* aiQ I j :=
 zvq (M:=(aje k n)⁰)
  (g:=(algebraMap _ (aiQ I j)).comp (substitute I j))
  (fun y=>z0j (M:=aXX I j)
    (aiQ I j) ⟨substitute I j y,y,y.property,rfl⟩)
instance gQy (I:znc (z3y σ k)) (j:Fin n→σ) :
 zZE S (aiQ I j) :=(exn I j).toAlgebra
theorem bsd (I:znc (z3y σ k)) (j:Fin n→σ)
  (r :aje k n) :
  algebraMap S (aiQ I j) (algebraMap (aje k n) S r) =
    algebraMap (ax2 (n:=n) I) (aiQ I j) (substitute I j r) :=
 zX4 _ _
abbrev weight (i:Option (Fin n)) :S :=
 algebraMap (aje k n) S (z9v i)
def bee (j:Fin n→σ) :z3y σ S :=
 (∑ i,C (weight (k :=k) (S:=S) (some i))*z9v (j i)) - C (weight (k :=k) (S:=S) (n:=n) none)
abbrev ke (I:znc (z3y σ k)) (j:Fin n→σ) :
  znc (z3y σ S) :=
 I.map (zDK (algebraMap k S)) ⊔ zye {bee (k :=k) j}
abbrev am9 (I:znc (z3y σ k)) (j:Fin n→σ) :=
 z3y σ S ⧸ ke (S:=S) I j
private def bnU (I:znc (z3y σ k)) (j:Fin n→σ) :
    (z3y σ k ⧸ I) →+* am9 (S:=S) I j :=
  zP2 I ((zVv _).comp (zDK (algebraMap k S)))
    (fun _p hp=>Ideal.Quotient.eq_zero_iff_mem.mpr
      (show _∈ke (S:=S) I j from
        (le_sup_left:I.map _≤ke (S:=S) I j) (z7X _ hp)))
private def aJ0 (I:znc (z3y σ k)) (j:Fin n→σ) :
  ax2 (n:=n) I →+* am9 (S:=S) I j :=
 eval₂Hom (bnU I j) (fun i=>algebraMap S _ (weight (k :=k) (some i)))
private theorem dl6 (I:znc (z3y σ k)) (j:Fin n→σ) :
    (aJ0 (S:=S) I j).comp (substitute I j) =
      (algebraMap S (am9 (S:=S) I j)).comp (algebraMap (aje k n) S) := by
  apply zXT
  · intro a
    simp only [zQb,substitute,eval₂Hom_C,aJ0,
      bnU,z0R,zpw]
    change _=algebraMap S (am9 (S:=S) I j)
      (algebraMap (aje k n) S (algebraMap k (aje k n) a))
    rw [← zG3 k (aje k n) S]
    rfl
  · intro i
    cases i with
    | some i=>simp [substitute,aJ0]
    | none =>
      have hz :zVv (ke (S:=S) I j) (bee (k :=k) j)=0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_right:zye {bee (k :=k) j} ≤ ke (S:=S) I j)
          (z5J _))
      simp only [bee,map_sub,map_sum,map_mul,sub_eq_zero] at hz
      simp only [zQb,substitute,eval₂Hom_X',Option.elim_none,
        bPX,aJ0,map_sum,map_mul,eval₂Hom_C,bnU,
        z0R,z7N]
      exact hz
private def azx (I:znc (z3y σ k)) (j:Fin n→σ) :
    aiQ I j →+* am9 (S:=S) I j :=
  zvq (M:=aXX I j)
    (g:=aJ0 (S:=S) I j) (by
      rintro ⟨_,r,hr,rfl⟩
      have h:=zmU (dl6 (S:=S) I j) r
      change aJ0 I j (substitute I j r) =
        algebraMap S _ (algebraMap (aje k n) S r) at h
      change IsUnit (aJ0 (S:=S) I j (substitute I j r))
      rw [h]
      exact (z0j S (⟨r,hr⟩: (aje k n)⁰)).map (algebraMap S _))
private theorem exU (I:znc (z3y σ k)) (j:Fin n→σ) :
  (azx (S:=S) I j).comp (algebraMap S (aiQ I j)) =
    algebraMap S (am9 (S:=S) I j) := by
 apply zuW (M:=(aje k n)⁰)
 apply zz4
 intro r
 have h:=zmU (dl6 (S:=S) I j) r
 simpa [zQb,bsd,azx,
  zX4] using h
private def ah2 (I:znc (z3y σ k)) (j:Fin n→σ) :
  z3y σ S →+* aiQ I j :=
 eval₂Hom (algebraMap S _) (fun i=>algebraMap (ax2 (n:=n) I) _
  (C (zVv I (z9v i))))
private theorem c4N (I:znc (z3y σ k)) (j:Fin n→σ) :
   (ah2 (S:=S) I j).comp (zDK (algebraMap k S)) =
     (algebraMap (ax2 (n:=n) I) _).comp (C.comp (zVv I)) := by
 apply zXT
 · intro a
   simp only [zQb,zpw,ah2,eval₂Hom_C]
   rw [zG3 k (aje k n) S,bsd]
   simp [substitute]
 · simp [ah2]
private def a8l (I:znc (z3y σ k)) (j:Fin n→σ) :
    am9 (S:=S) I j →+* aiQ I j :=
  zP2 _ (ah2 (S:=S) I j) (by
    apply show ke (S:=S) I j≤zdq (ah2 (S:=S) I j) from ?_
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro r hr
      change (ah2 (S:=S) I j).comp (zDK (algebraMap k S)) r=0
      rw [c4N]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    · intro r hr
      obtain rfl :=Set.mem_singleton_iff.mp hr
      change ah2 (S:=S) I j (bee (k :=k) j)=0
      rw [bee,map_sub,sub_eq_zero]
      rw [map_sum (ah2 (S:=S) I j)]
      simp only [map_mul]
      simp only [ah2,eval₂Hom_C,eval₂Hom_X',weight,
        bsd,substitute,Option.elim_none,Option.elim_some,
        bPX,map_sum,map_mul])
private theorem ex1 (I:znc (z3y σ k)) (j:Fin n→σ) :
   (a8l (S:=S) I j).comp (azx (S:=S) I j) =
     zz5 (aiQ I j) := by
 apply zuW (M:=aXX I j)
 simp only [RingHom.comp_assoc,azx,IsLocalization.lift_comp,
   RingHom.id_comp]
 apply zXT
 · intro r
   obtain ⟨p,rfl⟩:=zld r
   have h:=zmU (c4N (S:=S) I j) p
   simp only [aJ0,bnU,zQb,
     eval₂Hom_C,z0R]
   change ah2 (S:=S) I j (zDK (algebraMap k S) p)= _
   exact h
 · intro i
   simp only [zQb,aJ0,eval₂Hom_X']
   change ah2 (S:=S) I j (C (weight (k :=k) (some i))) =
     algebraMap (ax2 (n:=n) I) _ (z9v i)
   simp [ah2,bsd,substitute]
private theorem ex3 (I:znc (z3y σ k)) (j:Fin n→σ) :
    (azx (S:=S) I j).comp (a8l (S:=S) I j) =
      zz5 (am9 (S:=S) I j) := by
  apply zz4
  intro r
  obtain ⟨p,rfl⟩:=zld r
  have h: (azx (S:=S) I j).comp (ah2 (S:=S) I j) =
      zVv (ke (S:=S) I j) := by
    apply zXT
    · intro a
      change azx (S:=S) I j (ah2 I j (C a)) =
        algebraMap S (am9 (S:=S) I j) a
      simpa only [ah2,eval₂Hom_C,zQb] using
        zmU (exU (S:=S) I j) a
    · intro i
      simp [ah2,azx,zX4,
        aJ0,bnU]
  exact zmU h p
def efE (I:znc (z3y σ k)) (j:Fin n→σ) :
    am9 (S:=S) I j ≃ₐ[S] aiQ I j where
  __:=RingEquiv.ofRingHom (a8l (S:=S) I j) (azx (S:=S) I j)
    (ex1 I j) (ex3 I j)
  commutes' a := by
    change ah2 (S:=S) I j (C a)= _
    simp [ah2]
end OffsetLocalization
section RationalWeights
open cu gT DQ Cu
open MvPolynomial
open scoped Polynomial nonZeroDivisors
abbrev ae7 (E :Type) [zrb E] (n:ℕ) :=
 z3y (Fin n) (FractionRing E[X])
abbrev TK (E :Type) [zrb E] (n:ℕ) :=
 FractionRing (ae7 E n)
def RB {E F:Type} [zrb E] [zrb F] (f :E →+* F) :
    FractionRing E[X] →+* FractionRing F[X] :=
  zJ1 (j:=zhd f) (zTo f f.injective)
theorem drK {E F G:Type} [zrb E] [zrb F] [zrb G]
  (f :E →+* F) (g:F →+* G) :
  (RB g).comp (RB f)=RB (g.comp f) := by
 apply z2O (A:=E[X])
 intro p
 simp [RB,zJ1,zi7,zoi]
abbrev bK7 {E :Type} [zrb E] (a :E) :FractionRing E[X] :=
 algebraMap E[X] (FractionRing E[X]) (z1z a)
def pD {E :Type} [zrb E] {n:ℕ} (f :L →+* E) (a :Fin n→E) :
    SourceRing n →+* ae7 E n :=
  eval₂Hom (C.comp (RB f))
    (fun i=>i.elim (∑ j,z9v j*C (bK7 (a j))) z9v)
theorem c3v {E F:Type} [zrb E] [zrb F] {n:ℕ}
    (f :L →+* E) (g:E →+* F) (a :Fin n→E) :
    (zDK (RB g)).comp (pD f a) =
      pD (g.comp f) (g ∘ a) := by
  apply zXT
  · intro r
    simp only [zQb,pD,eval₂Hom_C,zpw]
    exact congrArg C (zmU (drK f g) r)
  · intro i
    cases i with
    | some i=>simp [pD]
    | none =>
      simp only [zQb,pD,eval₂Hom_X',Option.elim_none,
        map_sum,map_mul,z7N,zpw,RB,
        zJ1,zi7,zKC,zrL,
        z3s]
abbrev fZ {E :Type} [zrb E] [zZE L E] {n:ℕ} (a :Fin n→E) :=
 IntermediateField.adjoin L (zxp a)
def OX {E :Type} [zrb E] [zZE L E] {n:ℕ} (a :Fin n→E) :
    Fin n→fZ a :=
  fun i=>⟨a i,IntermediateField.subset_adjoin _ _ (zWL i)⟩
abbrev auB {E :Type} [zrb E] [zZE L E] {n:ℕ} (a :Fin n→E) :=
 pD (algebraMap L (fZ a)) (OX a)
theorem bnt {E :Type} [zrb E] [zZE L E] {n:ℕ}
   (a :Fin n→E) (h:zq4 (pD (algebraMap L E) a)) :
   zq4 (auB a) := by
 let F:=fZ a
 let g:F →+* E :=F.val.toRingHom
 have he : (zDK (RB g)).comp (auB a) =
     pD (algebraMap L E) a := by
   rw [auB,c3v]
   rfl
 have hi:zq4 ((zDK (RB g)).comp (auB a)) :=
   he.symm ▸ h
 intro x y hxy
 apply hi
 exact congrArg (zDK (RB g)) hxy
abbrev aww {E :Type} [zrb E] {n:ℕ} (f :SourceRing n →+* ae7 E n)
   (hf :zq4 f) :zZE (jY n) (TK E n) :=
 (zJ1 (j:=f) hf).toAlgebra
theorem bhm {E :Type} [zrb E] {n:ℕ} (f :SourceRing n →+* ae7 E n)
    (hf :zq4 f) (r :SourceRing n) :
    @algebraMap (jY n) (TK E n) _ _ (aww f hf)
        (algebraMap (SourceRing n) (jY n) r) =
      algebraMap (ae7 E n) (TK E n) (f r) :=
  zi7 (M:=(SourceRing n)⁰) (T:=(ae7 E n)⁰)
    (g:=f) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf) r
end RationalWeights
section SeedGraph
open cu gT DQ Cu
open MvPolynomial
open scoped nonZeroDivisors
variable {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
variable {R:wJ C₀ J g} (A:yI R n)
private def aVc :
  ax2 (n:=n) (EF A) →+* ae7 (oO C₀) n :=
 zDK (RingHom.kerLift (W8 A))
private theorem cUd:zq4 (aVc A) :=
 zNV _ (zuJ (W8 A))
private theorem cUc (i:Fin n) :
  aVc A (z9v i)=z9v i :=
 z7N _ _
private theorem cUb (p:Gc n) :
  aVc A (C (zVv (EF A) p))=C (W8 A p) :=
 zpw _ _
private theorem b5K :
    (aVc A).comp (substitute (EF A) Sum.inr) =
      pD (zT C₀) A.coordinate := by
  apply zXT
  · intro r
    simp only [zQb,substitute,pD,eval₂Hom_C,cUb,
      W8]
    rfl
  · intro i
    cases i with
    | some i =>
      simp only [zQb,substitute,pD,eval₂Hom_X',Option.elim_some,
        cUc]
    | none =>
      simp only [zQb,substitute,pD,eval₂Hom_X',Option.elim_none,
        bPX]
      rw [map_sum (aVc A)]
      apply zUo rfl
      intro i _
      rw [map_mul,cUc,cUb]
      simp only [W8,eval₂Hom_X',Sum.elim_inr,z3s]
      rfl
private def aH6 :
  aAM (EF A) ≃ₐ[jY n] aiQ (EF A) Sum.inr :=
 efE (k :=FX) (S:=jY n) (EF A) Sum.inr
theorem ekz (h : ¬ zq4
   (pD (zT C₀) A.coordinate)) :
   zOt (aAM (EF A)) := by
 classical
 have hker : ¬ ∀ p:SourceRing n,
     pD (zT C₀) A.coordinate p=0→p=0 :=
   fun hk=>h ((injective_iff_map_eq_zero _).mpr hk)
 obtain ⟨p,hp⟩:=not_forall.mp hker
 obtain ⟨hz,hp⟩:=not_imp.mp hp
 have hsub:substitute (EF A) Sum.inr p=0:= by
   apply cUd A
   rw [map_zero,← zQb,b5K,hz]
 let d:aXX (EF A) Sum.inr :=
   ⟨substitute (EF A) Sum.inr p,p,mem_nonZeroDivisors_iff_ne_zero.mpr hp,rfl⟩
 have hu:=z0j (M:=aXX (EF A) Sum.inr)
   (aiQ (EF A) Sum.inr) d
 change IsUnit (algebraMap _ _ (substitute (EF A) Sum.inr p)) at hu
 rw [hsub,map_zero] at hu
 let:zOt (aiQ (EF A) Sum.inr) :=
   subsingleton_iff_zero_eq_one.mp (isUnit_zero_iff.mp hu)
 exact (aH6 A).injective.subsingleton
theorem eks (h:zq4
    (pD (zT C₀) A.coordinate)) :
    letI:=aww (pD (zT C₀) A.coordinate) h
    ∃ f :aAM (EF A) →ₐ[jY n]
      TK (oO C₀) n,Function.Injective f := by
  let:=aww (pD (zT C₀) A.coordinate) h
  let B:=ax2 (n:=n) (EF A)
  let T:=aiQ (EF A) Sum.inr
  let E :=TK (oO C₀) n
  let M:=aXX (EF A) Sum.inr
  let q:B →+* E :=(algebraMap (ae7 (oO C₀) n) E).comp
    (aVc A)
  have hq:zq4 q:= by
    intro x y hxy
    apply cUd A
    exact zxb (ae7 (oO C₀) n) E hxy
  have hu (p:M) :IsUnit (q p) := by
    obtain ⟨d,hd,hd'⟩:=p.property
    change substitute (EF A) Sum.inr d=(p:B) at hd'
    rw [← hd']
    change IsUnit ((algebraMap (ae7 (oO C₀) n) E)
      (aVc A (substitute (EF A) Sum.inr d)))
    have hs :aVc A (substitute (EF A) Sum.inr d) =
        pD (zT C₀) A.coordinate d :=
      zmU (b5K A) d
    rw [hs]
    suffices hn:algebraMap (ae7 (oO C₀) n) E
        (pD (zT C₀) A.coordinate d)≠0 from hn.isUnit
    intro hz
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hd)
    apply h
    apply zxb (ae7 (oO C₀) n) E
    simpa only [map_zero] using hz
  let e :T →+* E :=zvq hu
  have he :zq4 e := by
    apply (IsLocalization.lift_injective_iff hu).mpr
    intro x y
    exact ⟨fun hxy=> by
      obtain ⟨d,hd⟩:=IsLocalization.exists_of_eq (M:=M) hxy
      exact (hu d).mul_left_cancel (by rw [← map_mul,← map_mul,hd]),
      fun hxy=>congrArg (algebraMap B T) (hq hxy)⟩
  have hc:e.comp (algebraMap (jY n) T)=algebraMap (jY n) E := by
    apply zuW (M:=(SourceRing n)⁰)
    apply zz4
    intro p
    simp only [zQb]
    have hs :=bsd (S:=jY n) (EF A) Sum.inr p
    rw [hs]
    have hl:e (algebraMap B T (substitute (EF A) Sum.inr p)) =
        q (substitute (EF A) Sum.inr p) :=
      zX4 hu _
    rw [hl,bhm]
    exact congrArg (algebraMap (ae7 (oO C₀) n) E)
      (zmU (b5K A) p)
  let φ:T →ₐ[jY n] E :=⟨e,zmU hc⟩
  exact ⟨φ.comp (aH6 A).toAlgHom,he.comp (aH6 A).injective⟩
end SeedGraph
end
end aFZ
end
section
set_option maxHeartbeats 600000
namespace aFZ
noncomputable section
open cu gT DQ Cu XW
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g n:ℕ)
    (R:wJ C₀ J g) (A:yI R n)
    (h:zq4 (pD (zT C₀) A.coordinate)),
    letI:zZE L (oO C₀) :=(zT C₀).toAlgebra
    letI:=aww (auB A.coordinate)
      (bnt A.coordinate h)
    zAa (jY n) (aYv A) →
    ∃ f :aYv A →ₐ[jY n]
      TK (fZ A.coordinate) n,zpX f
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g n:ℕ)
    (R:wJ C₀ J g) (A:yI R n)
    (h:zq4 (pD (zT C₀) A.coordinate)),
    letI:zZE L (oO C₀) :=(zT C₀).toAlgebra
    letI:=aww (auB A.coordinate)
      (bnt A.coordinate h)
    letI:=aww (pD (zT C₀) A.coordinate) h
    ∃ i:TK (fZ A.coordinate) n →ₐ[jY n]
        TK (oO C₀) n,
      letI:=i.toRingHom.toAlgebra
      zAa (TK (fZ A.coordinate) n)
          (TK (oO C₀) n) ∧
        zsE (TK (fZ A.coordinate) n)
          (TK (oO C₀) n)≤gY A
private theorem gDF {S B C F E :Type} [zrb S] [za6 B] [za6 C]
   [zrb F] [zrb E] [zZE S B] [zZE S C] [aF:zZE S F] [aE :zZE S E]
   (hC:zAa S C) (f :C →ₐ[S] F) (hf :zpX f)
   (j:B →ₐ[S] E) (hj:zq4 j) (i:F →ₐ[S] E) {d:ℕ}
   (hi:letI:=i.toRingHom.toAlgebra
     zAa F E∧zsE F E≤d) :
   zAa S B∧zsE S B≤d*zsE S C:= by
 let:=i.toRingHom.toAlgebra
 have :zsf S F E :=zKB i
 have :zAa S C:=hC
 have :zAa S F:=zIV f.toLinearMap hf
 have :zAa F E :=hi.1
 have :zAa S E :=Module.Finite.trans F E
 refine ⟨Module.Finite.of_injective j.toLinearMap hj,?_⟩
 calc
   zsE S B≤zsE S E :=j.toLinearMap.finrank_le_finrank_of_injective hj
   _=zsE S F*zsE F E :=(zS7 S F E).symm
   _≤d*zsE S C:= by
     rw [mul_comm (zsE S F)]
     exact Nat.mul_le_mul hi.2 (f.toLinearMap.finrank_le_finrank_of_surjective hf)
theorem of_children (h1 :c1) (h2 :c2) :XW.c2 := by
 intro C₀ _ J g n R A hfinite
 classical
 by_cases h:zq4 (pD (zT C₀) A.coordinate)
 · let:zZE L (oO C₀) :=(zT C₀).toAlgebra
   let coeffScalars :=aww (auB A.coordinate)
    (bnt A.coordinate h)
   let seedScalars :=aww (pD (zT C₀) A.coordinate) h
   obtain ⟨f,hf⟩:=h1 C₀ J g n R A h hfinite
   obtain ⟨i,hi⟩:=h2 C₀ J g n R A h
   obtain ⟨j,hj⟩:=eks A h
   exact gDF (S:=jY n) (B:=aAM (EF A))
    (C:=aYv A) (F:=TK (fZ A.coordinate) n)
    (E :=TK (oO C₀) n)
    (aF:=coeffScalars) (aE :=seedScalars) hfinite f hf j hj i hi
 · have :zOt (aAM (EF A)) :=ekz A h
   exact ⟨inferInstance,by simp [zuF]⟩
end
end aFZ
end
section
namespace czu
noncomputable section
open Algebra MvPolynomial cu gT DQ Cu
 XW aFZ
open scoped Polynomial BigOperators nonZeroDivisors
set_option maxHeartbeats 600000
private theorem aFj (k B:Type) [zrb k] [za6 B] [ztn B]
  [zZE k B] :trdeg k (FractionRing B)=trdeg k B:= by
 let:zjH B (FractionRing B) :=
  (zE4 (K:=FractionRing B)).mpr inferInstance
 rw [← trdeg_add_eq k B,trdeg_eq_zero (R:=B),add_zero]
private theorem gEc {k B:Type} [zrb k] [za6 B] [ztn B]
  [zZE k B] {d:ℕ} (u:z3y (Fin d) k →ₐ[k] B)
  (hu:zq4 u) (hfin:u.Finite) :trdeg k B=d:= by
 let P:=z3y (Fin d) k
 let:zZE P B:=u.toRingHom.toAlgebra
 let:zsf k P B:=zKB u
 let:FaithfulSMul P B:=(faithfulSMul_iff_algebraMap_injective P B).mpr hu
 let:zAa P B:=hfin
 rw [← trdeg_add_eq k P,trdeg_eq_zero (R:=P),add_zero,
  zUx,Cardinal.lift_id,Cardinal.mk_fin]
private theorem bNK (C₀:sQ) [hC:Fact (Irreducible C₀)] :
   trdeg L (oO C₀)≤1 := by
 let B:=abz C₀
 obtain ⟨d,u,hu,hfin⟩:=exists_finite_inj_algHom_of_fg L B
 have hdim: (affineHilbertPolynomial (auG C₀)).natDegree≤1 := by
   simpa using natDegree_affineHilbertPolynomial_le_of_mem (I:=auG C₀)
     hC.out.ne_zero (z5J C₀)
 rw [natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective u hfin hu,
   zJa] at hdim
 rw [aFj L B,gEc u hu hfin]
 exact_mod_cast hdim
private theorem drL {F E :Type} [zrb F] [zrb E] (f :F →+* E)
  (a :F) :RB f (bK7 a)=bK7 (f a) := by
 simp [RB,zJ1,zi7]
private theorem dM5 {E :Type} [zrb E] [zZE L E] {n:ℕ}
   (a :Fin n→E) (h:zq4 (pD (algebraMap L E) a)) :
   1≤trdeg L (fZ a) := by
 classical
 apply Cardinal.one_le_iff_ne_zero.mpr
 intro hz
 let:zjH L (fZ a) :=trdeg_eq_zero_iff.mp hz
 have he :fZ a = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
 have ha (j:Fin n) : ∃ b:L,algebraMap L E b=a j:= by
   have hm:a j∈fZ a :=IntermediateField.subset_adjoin _ _ (zWL j)
   rw [he,IntermediateField.mem_bot] at hm
   exact hm
 choose b hb using ha
 have hrel : (z9v none :SourceRing n) =
     ∑ j:Fin n,z9v (some j)*C (bK7 (b j)) := by
   apply h
   simp only [pD,eval₂Hom_X',Option.elim_none,map_sum,map_mul,Option.elim_some,
     eval₂Hom_C,zQb,drL,hb]
 have hbad:=congrArg (zY9 (fun i:Option (Fin n)=>i.elim (1 :FX) (fun _=>0)))
   hrel
 simp at hbad
private theorem bg9 (C₀:sQ) [Fact (Irreducible C₀)] {n:ℕ}
   (a :Fin n→ oO C₀)
   (h:zq4 (pD (zT C₀) a)) :
   letI:zZE L (oO C₀) :=(zT C₀).toAlgebra
   zAa (fZ a) (oO C₀) := by
 let standardAlgebra :zZE L (oO C₀) :=inferInstance
 have hstandard : @zl5 L (oO C₀) _ _ standardAlgebra := by
   let:zl5 (abz C₀) (oO C₀) :=
     zrU _ (abz C₀)⁰
   exact zQi L (abz C₀) (oO C₀)
 have halgebra :standardAlgebra=(zT C₀).toAlgebra :=
   Algebra.algebra_ext _ _ fun _=>rfl
 let:zZE L (oO C₀) :=(zT C₀).toAlgebra
 let F:=fZ a
 let:FaithfulSMul L F :=
   (faithfulSMul_iff_algebraMap_injective L F).mpr (algebraMap L F).injective
 let:FaithfulSMul F (oO C₀) :=
   (faithfulSMul_iff_algebraMap_injective F _).mpr (algebraMap F (oO C₀)).injective
 have hF:1≤trdeg L F:=dM5 a h
 have hE :trdeg L (oO C₀)≤1 :=
   Eq.mp (congrArg (fun alg:zZE L (oO C₀) =>
     letI:=alg
     trdeg L (oO C₀)≤1) halgebra) (bNK C₀)
 have hsum:trdeg F (oO C₀)+1≤0+1 := calc
   trdeg F (oO C₀)+1≤trdeg F (oO C₀)+trdeg L F :=
     add_le_add_right hF _
   _=trdeg L (oO C₀) := by rw [add_comm,trdeg_add_eq L F]
   _≤0+1 := by simpa using hE
 let:zjH F (oO C₀) :=trdeg_eq_zero_iff.mp
   (le_antisymm ((Cardinal.add_le_add_iff_of_lt_aleph0 Cardinal.one_lt_aleph0).mp hsum) bot_le)
 let E :=oO C₀
 let:zl5 L E :=
   Eq.mp (congrArg (fun alg => @zl5 L (oO C₀) _ _ alg)
     halgebra) hstandard
 let:zl5 F E :=z9q L F E
 exact zNf
section RationalExtension
attribute [local instance] Polynomial.algebra MvPolynomial.algebraMvPolynomial
private abbrev drJ {F E :Type} [zrb F] [zrb E] [zZE F E] :
  zZE (FractionRing F[X]) (FractionRing E[X]) :=
 FractionRing.liftAlgebra F[X] (FractionRing E[X])
attribute [local instance] drJ
private abbrev gL1 {F E :Type} [zrb F] [zrb E] [zZE F E] {n:ℕ} :
  zZE (TK F n) (TK E n) :=
 FractionRing.liftAlgebra (ae7 F n) (TK E n)
attribute [local instance] gL1
private theorem drN {F E :Type} [zrb F] [zrb E] [zZE F E] :
   algebraMap (FractionRing F[X]) (FractionRing E[X])=RB (algebraMap F E) := by
 apply z2O (A:=F[X])
 intro p
 change zIj (FaithfulSMul.algebraMap_injective F[X] (FractionRing E[X]))
     (algebraMap F[X] (FractionRing F[X]) p)= _
 rw [zoc,zG3 F[X] E[X] (FractionRing E[X])]
 simp [RB,zJ1,zi7]
private def gL4 {F E :Type} [zrb F] [zrb E] [zZE F E] {n:ℕ}
   (p:SourceRing n →+* ae7 F n) (hp:zq4 p)
   (q:SourceRing n →+* ae7 E n) (hq:zq4 q)
   (h: (zDK (RB (algebraMap F E))).comp p=q) :
   letI:=aww p hp
   letI:=aww q hq
   TK F n →ₐ[jY n] TK E n:= by
 let:=aww p hp
 let:=aww q hq
 let P:=ae7 F n
 let Q:=ae7 E n
 let F' := TK F n
 let E' := TK E n
 refine ⟨algebraMap F' E',?_⟩
 suffices he : (algebraMap F' E').comp (algebraMap (jY n) F') =
     algebraMap (jY n) E' from zLs he
 apply z2O (A:=SourceRing n)
 intro r
 change algebraMap F' E' (algebraMap (jY n) F'
   (algebraMap (SourceRing n) (jY n) r))= _
 rw [bhm,bhm]
 change zIj (FaithfulSMul.algebraMap_injective P E')
     (algebraMap P F' (p r))= _
 rw [zoc,zG3 P Q E']
 rw [zu8,drN]
 exact congrArg (algebraMap Q E') (zmU h r)
private theorem gL8 {F E :Type} [zrb F] [zrb E] [zZE F E]
    [zAa F E] (n:ℕ) :
    zAa (TK F n) (TK E n) ∧
      zsE (TK F n) (TK E n) =
        Module.finrank F E := by
  have hrX:z1x (FractionRing F[X]) (FractionRing E[X])=z1x F E :=
    Algebra.IsAlgebraic.rank_fractionRing_polynomial
  let:zAa (FractionRing F[X]) (FractionRing E[X]) := by
    apply Module.rank_lt_aleph0_iff.mp
    rw [hrX]
    exact Module.rank_lt_aleph0_iff.mpr inferInstance
  have hrW:z1x (TK F n) (TK E n) =
      Module.rank F E := by
    rw [Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R:=FractionRing F[X])
      (S:=FractionRing E[X]) (Fin n),Cardinal.lift_id,hrX]
  refine ⟨Module.rank_lt_aleph0_iff.mp ?_,congrArg Cardinal.toNat hrW⟩
  rw [hrW]
  exact Module.rank_lt_aleph0_iff.mpr inferInstance
end RationalExtension
theorem proof :aFZ.c2 := by
 intro C₀ _ J g n R A h
 let:zZE L (oO C₀) :=(zT C₀).toAlgebra
 let F:=fZ A.coordinate
 let E :=oO C₀
 let p:=auB A.coordinate
 let q:=pD (zT C₀) A.coordinate
 have hp:zq4 p:=bnt A.coordinate h
 have he : (zDK (RB (algebraMap F E))).comp p=q:= by
   change (zDK (RB (algebraMap F E))).comp
     (auB A.coordinate)=q
   rw [auB,c3v]
   rfl
 let:zAa F E :=bg9 C₀ A.coordinate h
 refine ⟨gL4 p hp q h he,?_⟩
 have hw:=gL8 (F:=F) (E :=E) n
 exact ⟨hw.1,hw.2.le⟩
end
end czu
end
section
namespace aiN
noncomputable section
open cu gT DQ Cu XW MvPolynomial
open scoped Polynomial
private theorem gt1 {n:ℕ} (P:XO n) (t:Fin n→L) :
    zY9 (algebraMap L aQ ∘ t) (aIM P) =
      ((specialize P t).map (algebraMap L[X] FX)).eval₂
        (algebraMap FX aQ) (ek 1) := by
  let e :=zY9 (algebraMap L aQ ∘ t)
  let m:=zDK (algebraMap FX aQ) (σ:=Fin n)
  let v :=e.comp m
  let ξ:=algebraMap L[X] FX z7y
  let α:=(algebraMap FX aQ).comp (algebraMap L[X] FX)
  have hC:v.comp (zDK (algebraMap L FX)) =
      (algebraMap L aQ).comp (zY9 t) := by
    apply zXT
    · intro a
      simpa only [v,e,m,zQb,zpw,MvPolynomial.eval_C]
        using (zG3 L FX aQ a).symm
    · intro i
      simp [v,e,m]
  have hX:v.comp (zqf (zDK (algebraMap L FX))
      (znf ξ))= α.comp (zhd (zY9 t)) := by
    apply z86
    · intro a
      simp only [zQb,z4Q,zJU,
        zKC,zrL]
      rw [show v (zDK (algebraMap L FX) a) =
        algebraMap L aQ (zY9 t a) from zLs hC a]
      change algebraMap L aQ (zY9 t a) =
        algebraMap FX aQ (algebraMap L[X] FX (algebraMap L L[X] (zY9 t a)))
      rw [← zG3 L L[X] FX,← zG3 L FX aQ]
    · simp [v,m,e,ξ,α]
  change e ((ajx P).eval₂ m (znf (ek 1)))= _
  rw [zly]
  rw [show e (znf (ek 1))=ek 1 by simp [e]]
  change (ajx P).eval₂ v (ek 1)= _
  unfold ajx specialize
  rw [zem]
  change P.eval₂ (v.comp (zqf (zDK (algebraMap L FX))
    (znf ξ))) (ek 1)= _
  rw [hX,zem,zem]
private theorem efW :
    zq4 (zqf (algebraMap FX aQ) (ek 1)) := by
  let ι:=(algebraMap aZ aQ).comp (z3n (R:=FX)
    (1 :Fin 2)).toRingHom
  have he :zqf (algebraMap FX aQ) (ek 1)=ι:= by
    apply z86
    · intro a
      change (z1z a).eval₂ (algebraMap FX aQ) (ek 1) =
        algebraMap aZ aQ ((z3n (1 :Fin 2)) (z1z a))
      rw [zJU,Polynomial.toMvPolynomial_C]
      exact zG3 FX aZ aQ a
    · simp [ι,ek]
  rw [he]
  exact (zxb aZ aQ).comp (Polynomial.toMvPolynomial_injective 1)
theorem eHV {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n)
    (q:DT n) (hq:q∉TU A) :
    IsUnit (zVv _
      (zDK (algebraMap L aQ) q) :anh A) := by
  classical
  let I:=TU A
  let s :=zDK (algebraMap L aQ) (σ:=Fin n)
  let π:z3y (Fin n) aQ →+* anh A:=zVv _
  change IsUnit (π (s q))
  by_contra hn
  obtain ⟨M,hM,hqM⟩:=exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
  let:M.IsMaximal:=hM
  let E :=anh A ⧸ M
  let ψ:z3y (Fin n) aQ →+* E :=(zVv M).comp π
  let ρ:DT n →+* E :=ψ.comp s
  let T:=zdq ρ
  let:T.IsPrime :=zgL ρ
  have hIT:I≤T:= by
    intro r hr
    apply RingHom.mem_ker.mpr
    change zVv M (π (s r))=0
    rw [show π (s r)=0 from Ideal.Quotient.eq_zero_iff_mem.mpr ?_,map_zero]
    apply zKg
    change zDK (algebraMap L aQ) r ∈
      I.map (zDK (algebraMap L aQ))
    exact z7X _ hr
  have hle :I ⊔ zye {q} ≤ T :=
    sup_le hIT (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hqM))))
  have hI:I.IsPrime :=zgL _
  have hd:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hI hq (le_rfl :q.totalDegree≤q.totalDegree)).1
  have hdim: (affineHilbertPolynomial I).natDegree≤1 :=(aTz A).2
  let:zAa L (DT n ⧸ (I ⊔ zye {q})) :=
    natDegree_affineHilbertPolynomial_eq_zero_iff.mp (by omega)
  let B:=DT n ⧸ T
  let:zAa L B:=zIV
    (z5F L hle).toLinearMap (zuo hle)
  choose t ht using fun i:Fin n =>
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k :=L) (K:=B)).2
      (zVv T (z9v i))
  let β:=ψ.comp znf
  have hψ:ψ=β.comp (zY9 (algebraMap L aQ ∘ t)) := by
    apply zXT
    · simp [β]
    · intro i
      simp only [β,zQb,MvPolynomial.eval_X,z3s]
      have hi:zVv T (znf (t i)) =
          zVv T (z9v i) :=ht i
      have he :=congrArg (zP2 T ρ (fun _ hx=>RingHom.mem_ker.mp hx)) hi
      simpa only [z0R,ρ,s,zQb,
        zpw,z7N] using he.symm
  have htI (r :DT n) (hr :r∈I) :zY9 t r=0:= by
    have hz :ψ (s r)=0:=RingHom.mem_ker.mp (hIT hr)
    rw [hψ,zQb,show s r=zDK (algebraMap L aQ) r from rfl,
      MvPolynomial.eval_map,← z6r] at hz
    exact (β.injective.comp (algebraMap L aQ).injective) (by simpa using hz)
  have hnonzero :specialize A.equation t≠0:= by
    intro hzero
    have htzero : ∀ i,t i=0:= by
      intro i
      obtain ⟨j,k,h⟩:=cGE A i
      have hp:=congrArg (fun P: (L[X])[X]=>(P.coeff j).coeff k) hzero
      simp only [specialize,z0b,zKC,
        zO6] at hp
      simpa [map_sub,hp] using htI _ h
    obtain ⟨ℓ,hℓ⟩:=cGD A
    simpa [htzero] using htI _ hℓ
  have hcut:ψ (aIM A.equation)=0:= by
    change zVv M (π (aIM A.equation))=0
    rw [show π (aIM A.equation)=0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (zs0 (z5J _)),
      map_zero]
  rw [hψ,zQb] at hcut
  have hz :=β.injective (hcut.trans (map_zero β).symm)
  rw [gt1] at hz
  apply hnonzero
  have hi:=zTo (algebraMap L[X] FX) (zxb L[X] FX)
  apply hi
  exact efW (by simpa using hz)
end
end aiN
end
section
namespace Ey
noncomputable section
open B7 MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
def adN {σ F:Type*} [zrb F] (P:znc (z3y σ F)) :
    znc (z3y σ F) :=
  zye ((fun f :z3y σ F=>homogeneousComponent f.totalDegree f) '' (P:Set _))
def aVq (J:znc mK) :znc nW:=J.comap tO
abbrev l5:=z3y (Fin 2) dF
abbrev MY:=FractionRing l5
def aWi (L:Fin 2→nW) (J:znc mK) :
    l5 →ₐ[dF] (mK ⧸ J) :=
  (zvR dF J).comp (tO.comp (aeval L))
abbrev ay5 (L:Fin 2→nW) (J:znc mK) :Type :=
 letI:zeq l5 (mK ⧸ J) :=
  zki (mK ⧸ J)
   (show l5 →+* (mK ⧸ J) from (aWi L J).toRingHom)
 MY ⊗[l5] (mK ⧸ J)
def adI (L:Fin 2→nW) (J:znc mK) :ℕ :=
 zsE MY (ay5 L J)
def afO (L:Fin 2→nW) (J:znc nW) :
    l5 →ₐ[dF] (nW ⧸ J) :=
  (zvR dF J).comp (aeval L)
def agE (L:Fin 2→nW) (J:znc nW) :Prop :=
  (∀ i,(L i).IsHomogeneous 1) ∧ @RingHom.Finite l5 (nW ⧸ J) _ _
    (afO L J).toRingHom
theorem agE.of_le {L:Fin 2→nW} {J J' : znc nW}
  (h:agE L J) (hle :J≤J') :agE L J' := by
 refine ⟨h.1,?_⟩
 have hcomp:afO L J' = (z5F dF hle).comp (afO L J) := by
  unfold afO
  ext i
  simp
 rw [hcomp]
 exact zfr
  (zO7 _ (zuo hle)) h.2
end
end Ey
end
section
namespace aiN
noncomputable section
open cu gT DQ Cu UI XW
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g n:ℕ)
    (R:wJ C₀ J g) (A:yI R n),
    0<g→zAa aQ (anh A)→Nontrivial (anh A) →
    (∀ q:DT n,q∉TU A →
      IsUnit (zVv _
        (zDK (algebraMap L aQ) q) :anh A)) →
    ∃ e :anh A ≃+* Jv (akF A),
      aYW (aq1 A) (bcB A)
        (e.toRingHom.comp (algebraMap aQ (anh A)))
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g:ℕ)
    (R:wJ C₀ J g),
    zAa aQ (SI J) →
    ∀ b:aQ →+* Jv (EC R),
      aYW (amB R) (aW2 R) b →
      ∃ e :SI J ≃+* Jv (EC R),
        e.toRingHom.comp (algebraMap aQ (SI J))=b
def c3:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM) (g n:ℕ)
    (R:wJ C₀ J g) (A:yI R n),
    0<g→an8 (ZR (auC A))=gY A
private theorem gnP {k U V D E :Type} [zrb k] [zrb U] [zrb V]
   [za6 D] [za6 E] [zZE k D] [zZE k E]
   (e :D ≃+* U) (e' : E ≃+* V) (f :U →+* V)
   (h:e'.toRingHom.comp (algebraMap k E) =
     f.comp (e.toRingHom.comp (algebraMap k D))) :
   zsE k D *an8 f=zsE k E := by
 let a :k →+* U:=e.toRingHom.comp (algebraMap k D)
 let b:k →+* V:=f.comp a
 let:zZE k U:=a.toAlgebra
 let:zZE k V:=b.toAlgebra
 let:zZE U V:=f.toAlgebra
 let:zsf k U V:=zsL (R:=k) (S:=U) (A:=V)
   fun _=>rfl
 let eu:D ≃ₐ[k] U := { e with commutes' := fun _=>rfl }
 let ev :E ≃ₐ[k] V := { e' with commutes' := fun x=>zLs h x }
 change zsE k D *zsE U V=zsE k E
 rw [eu.toLinearEquiv.finrank_eq,ev.toLinearEquiv.finrank_eq]
 exact zS7 k U V
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :
    XW.c3:= by
  classical
  intro C₀ _ J g n R A hg hroot hord
  by_cases hne :Nontrivial (anh A)
  · obtain ⟨e,ha,hy,hs⟩:=h1 C₀ J g n R A hg hord hne (eHV A)
    let U:=Jv (akF A)
    let V:=Jv (EC R)
    let f :U →+* V:=ZR (auC A)
    let a :aQ →+* U:=e.toRingHom.comp (algebraMap aQ (anh A))
    let b:aQ →+* V:=f.comp a
    have hb:aYW (amB R) (aW2 R) b:= by
      refine ⟨?_,?_,?_⟩
      · intro x
        change f (a (algebraMap FX aQ x))= _
        rw [show a (algebraMap FX aQ x)= _ from ha x]
        exact bsi _ _
      · change f (a (ek 1))= _
        rw [show a (ek 1)= _ from hy]
        exact bsi _ _
      · change f (a (ek 0))= _
        rw [show a (ek 0)= _ from hs]
        exact cZf _
    obtain ⟨e',he'⟩:=h2 C₀ J g R hroot b hb
    have hd:an8 f=gY A:=h3 C₀ J g n R A hg
    apply le_of_eq
    rw [← hd,Nat.mul_comm]
    exact gnP e e' f he'
  · let:zOt (anh A) :=not_nontrivial_iff_subsingleton.mp hne
    rw [Module.finrank_eq_zero_of_subsingleton,Nat.mul_zero]
    exact zD0 _
end
end aiN
end
section
namespace Ey
noncomputable section
open aR B7 MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 :Prop :=
  ∀ (Q:znc jo) (L:Fin 2→nW),
    Q.IsPrime→Q.IsHomogeneous (homogeneousSubmodule rS ao) →
    (affineHilbertPolynomial Q).natDegree=2→agE L (aVq (oV Q)) →
    2*affineDegree Q ≤
      (133671 :ℚ)*(adI L (oV Q) :ℚ)
def c2 :Prop :=
  ∀ (P:znc jo),P.IsPrime→(affineHilbertPolynomial P).natDegree=2 →
    ∃ (n:ℕ) (Q:Fin n→ znc jo),
      (∀ i,Q i∈(adN P).minimalPrimes ∧
        (Q i).IsHomogeneous (homogeneousSubmodule rS ao) ∧
        (affineHilbertPolynomial (Q i)).natDegree=2) ∧
      affineDegree P = ∑ i,affineDegree (Q i) ∧
      ∀ (L:Fin 2→nW),zAa MY
        (ay5 L (oV (adN P))) →
        (∑ i,adI L (oV (Q i))) ≤
          adI L (oV (adN P))
def c3:Prop :=
  ∀ (P:znc jo) (g d:nW),XP P g d →
    ∃ L:Fin 2→nW,
      agE L (aVq (oV (adN P))) ∧
      zAa MY (ay5 L (oV (adN P))) ∧
      adI L (oV (adN P))≤g.totalDegree
end
end Ey
end
section
namespace bz1
noncomputable section
open cu gT DQ Cu UI XW aiN
open scoped Polynomial
set_option maxHeartbeats 600000
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:znc kM} {g n:ℕ}
variable {R:wJ C₀ J g}
private def xg (A:yI R n) :
  letI:zZE L (oO C₀) :=(zT C₀).toAlgebra
  IntermediateField L (oO C₀) :=
 letI:zZE L (oO C₀) :=(zT C₀).toAlgebra
 IntermediateField.adjoin L (zxp A.coordinate)
private abbrev XR (A:yI R n) := ↥(xg A)
private def bHM (A:yI R n) :L →+* XR A :=
 let:zZE L (oO C₀) :=(zT C₀).toAlgebra
 algebraMap L (XR A)
private def bCw (A:yI R n) (i:Fin n) :XR A:= by
 let:zZE L (oO C₀) :=(zT C₀).toAlgebra
 exact ⟨A.coordinate i,IntermediateField.subset_adjoin L _ ⟨i,rfl⟩⟩
private def pO (A:yI R n) :
  Jv (XR A) →+* y7 C₀:= by
 let:zZE L (oO C₀) :=(zT C₀).toAlgebra
 exact ZR (xg A).val.toRingHom
private def auy (A:yI R n) : (Jv (XR A))[X] :=
 (A.equation.map (zhd
   (zOD (bHM A) (bCw A)))).map
     (algebraMap (XR A)[X] (Jv (XR A)))
private theorem bWR (A:yI R n) :
    (auy A).map (pO A) =
      z1z (Mu C₀ (A.scale :oO C₀))*K8 R:= by
  let:zZE L (oO C₀) :=(zT C₀).toAlgebra
  let u:DT n →+* XR A :=
    zOD (bHM A) (bCw A)
  let v :DT n →+* oO C₀ :=
    zOD (zT C₀) A.coordinate
  have huv : (xg A).val.toRingHom.comp u=v := by
    dsimp only [u,v]
    rw [MvPolynomial.comp_eval₂Hom]
    rfl
  have hm: (pO A).comp ((algebraMap (XR A)[X] (Jv (XR A))).comp
      (zhd u))=(F5 C₀).comp (zhd v) := by
    apply zz4
    intro p
    change ZR (xg A).val.toRingHom (algebraMap _ _ (p.map u)) =
      F5 C₀ (p.map v)
    rw [b8y,zoi,huv]
    rfl
  calc
    (auy A).map (pO A) =
        (A.equation.map (zhd v)).map (F5 C₀) := by
      change ((A.equation.map (zhd u)).map
        (algebraMap _ _)).map (pO A)= _
      simp only [zoi,hm]
    _ = _:= by
      rw [show A.equation.map (zhd v)= _ from A.generic_eq,
        zNl,zrL]
      rfl
private theorem dH1 (A:yI R n) :
    Irreducible (auy A) := by
  let f :=zhd (pO A)
  let:IsLocalHom f :=
    ⟨fun p hp=>Polynomial.isUnit_iff_degree_eq_zero.mpr <| by
      simpa only [f,zKC,Polynomial.degree_map] using
        (Polynomial.isUnit_iff_degree_eq_zero.mp hp)⟩
  apply Irreducible.of_map (f :=f)
  change Irreducible ((auy A).map (pO A))
  rw [bWR,irreducible_isUnit_mul]
  · exact R.irreducible
  · exact (A.scale.isUnit.map (Mu C₀)).map z1z
private theorem c8R (R:wJ C₀ J g) :
   (K8 R).natDegree=g :=
 (Polynomial.natDegree_map_eq_of_injective (zxb _ _) _).trans R.degree
private theorem bWQ (A:yI R n) :
  (auy A).natDegree=g:= by
 rw [← Polynomial.natDegree_map (p:=auy A) (pO A),bWR,
  Polynomial.natDegree_C_mul ((A.scale.isUnit.map (Mu C₀)).ne_zero),
  c8R]
private def aW1 (A:yI R n) :
   Jv (XR A) →+* EC R :=
 (AdjoinRoot.of (K8 R)).comp (pO A)
private theorem c8P (A:yI R n) :
  (aW1 A).comp (ZR (bHM A))=amB R:= by
 let:zZE L (oO C₀) :=(zT C₀).toAlgebra
 change (AdjoinRoot.of (K8 R)).comp
  ((ZR (xg A).val.toRingHom).comp (ZR (bHM A)))= _
 rw [eyS]
 rfl
private theorem c4P {E F:Type} [zrb E] [zrb F]
   (S:Subfield F) (f :E[X] →+* F) (hc : ∀ a,f (z1z a)∈S)
   (hx :f z7y∈S) (p:E[X]) :f p∈S:= by
 induction p using zCU with
 | add p q hp hq=>exact (map_add f p q).symm ▸ S.add_mem hp hq
 | monomial n a =>
   rw [← zoT,map_mul,map_pow]
   exact S.mul_mem (hc a) (S.pow_mem hx n)
private theorem c8Q (A:yI R n) (x :Jv (XR A)) :
    aW1 A x∈bcC A:= by
  let:zZE L (oO C₀) :=(zT C₀).toAlgebra
  let:zZE FX (EC R) :=(amB R).toAlgebra
  let B:=bcC A
  have hcoef : (xg A).toSubfield≤B.toSubfield.comap (LW R) := by
    change (IntermediateField.adjoin L (zxp A.coordinate)).toSubfield≤_
    rw [IntermediateField.adjoin_toSubfield,Subfield.closure_le]
    rintro _ (⟨a,rfl⟩ | ⟨i,rfl⟩)
    · change AdjoinRoot.of (K8 R) (IN (oO C₀) (zT C₀ a))∈B
      have ha :=B.algebraMap_mem (IN L a)
      change amB R (IN L a)∈B at ha
      change AdjoinRoot.of (K8 R) (ZR (zT C₀) (IN L a))∈B at ha
      simpa only [bsi] using ha
    · exact IntermediateField.subset_adjoin FX _
        (zt3 _ ⟨i,rfl⟩)
  let j: (XR A)[X] →+* EC R :=
    (aW1 A).comp (algebraMap _ _)
  have hp : ∀ p,j p∈B:= by
    apply c4P B.toSubfield j
    · intro a
      change aW1 A (IN (XR A) a)∈B
      change AdjoinRoot.of (K8 R)
        (ZR (xg A).val.toRingHom (IN (XR A) a))∈B
      rw [bsi]
      exact hcoef a.property
    · change aW1 A (awC (XR A))∈B
      have hx :=B.algebraMap_mem (awC L)
      change amB R (awC L)∈B at hx
      have h:=zLs (c8P A) (awC L)
      simp only [zQb,cZf] at h
      exact (congrArg (fun z :EC R=>z∈B) h).mpr hx
  obtain ⟨p,q,_,rfl⟩:=zJC (XR A)[X] x
  rw [map_div₀]
  exact B.div_mem (hp p) (hp q)
private theorem dM2 (A:yI R n) :
    ∃ j:Jv (XR A) →+* akF A,
      (auC A).comp j=aW1 A∧an8 j=g:= by
  let:zZE L (oO C₀) :=(zT C₀).toAlgebra
  let:zZE FX (EC R) :=(amB R).toAlgebra
  let B:=bcC A
  let q:=auy A
  let:Fact (Irreducible q) :=⟨dH1 A⟩
  have hdvd:K8 R∣q.map (pO A) := by
    rw [show q.map (pO A)= _ from bWR A]
    exact dvd_mul_left _ _
  let f :=AdjoinRoot.map (pO A) q (K8 R) hdvd
  have hconst (x :Jv (XR A)) :f (AdjoinRoot.of q x)=aW1 A x :=
    AdjoinRoot.map_of _ _ _ _ _
  have hy :f (AdjoinRoot.root q)=aW2 R:=AdjoinRoot.map_root _ _ _ _
  have hf : ∀ w,f w∈B:= by
    intro w
    obtain ⟨p,rfl⟩:=AdjoinRoot.mk_surjective w
    exact c4P B.toSubfield (f.comp (AdjoinRoot.mk q))
      (fun a=> by
        rw [zQb,AdjoinRoot.mk_C,hconst,IntermediateField.mem_toSubfield]
        exact c8Q A a)
      (by
        rw [zQb,AdjoinRoot.mk_X,hy,IntermediateField.mem_toSubfield]
        exact (bcB A).property) p
  have hrange :B.toSubfield≤f.fieldRange := by
    change (IntermediateField.adjoin FX
      (zxp (fun i=>LW R (A.coordinate i)) ∪ {aW2 R})).toSubfield≤_
    rw [IntermediateField.adjoin_toSubfield,Subfield.closure_le]
    rintro _ (⟨x,rfl⟩ | (⟨i,rfl⟩ | hx))
    · change amB R x∈f.fieldRange
      rw [← c8P A,zQb,← hconst]
      exact f.mem_fieldRange_self _
    · let x :=IN (XR A) (bCw A i)
      refine ⟨AdjoinRoot.of q x,?_⟩
      rw [hconst]
      change AdjoinRoot.of (K8 R) (ZR (xg A).val.toRingHom x)= _
      rw [show x=IN (XR A) (bCw A i) from rfl,bsi]
      rfl
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨AdjoinRoot.root q,hy⟩
  let j:=(aW1 A).codRestrict B (c8Q A)
  refine ⟨j,rfl,?_⟩
  let:zZE (Jv (XR A)) (akF A) :=j.toAlgebra
  let fB:=f.codRestrict B hf
  let fA:AdjoinRoot q →ₐ[Jv (XR A)] akF A :=
    { fB with
      commutes' := fun x=>Subtype.ext (hconst x) }
  let e :=AlgEquiv.ofBijective fA ⟨fB.injective,fun z=> by
    obtain ⟨w,hw⟩:=hrange z.property
    exact ⟨w,Subtype.ext hw⟩⟩
  change zsE (Jv (XR A)) (akF A)=g
  rw [← e.toLinearEquiv.finrank_eq]
  exact finrank_quotient_span_eq_natDegree.trans (bWQ A)
theorem proof :aiN.c3:= by
 intro C₀ _ J g n R A hg
 let:zZE L (oO C₀) :=(zT C₀).toAlgebra
 have hseed :an8 (pO A)=gY A :=
  (cJ3 (xg A).val.toRingHom).trans cJS
 have hroot :an8 (AdjoinRoot.of (K8 R))=g:= by
  rw [← AdjoinRoot.algebraMap_eq,cJS]
  exact finrank_quotient_span_eq_natDegree.trans (c8R R)
 obtain ⟨j,hj,hd⟩:=dM2 A
 have hbig:=degree_comp (pO A) (AdjoinRoot.of (K8 R))
 have hsmall:=degree_comp j (auC A)
 rw [hroot,hseed] at hbig
 rw [hd,hj] at hsmall
 rw [cJ3]
 apply Nat.mul_left_cancel hg
 exact hsmall.trans (hbig.symm.trans (Nat.mul_comm _ _))
end
end bz1
end
section
namespace Pw
noncomputable section
open aR B7 Ey
open scoped Polynomial TensorProduct
abbrev yI {k :Type} [zrb k] {n:ℕ}
  (Q:znc (z3y (Fin n) k)) (i:Fin n) :=
 z3y (Fin n) k ⧸ (Q ⊔ zye {z9v i - 1})
abbrev ChartRing (Q:znc jo) (i:rS) :=yI Q i
def ayi {k :Type} [zrb k] {n:ℕ}
    (Q:znc (z3y (Fin n) k)) (i:Fin n) : (yI Q i)[X] :=
  ∑ j:Fin n,zdM j.val (zVv _ (z9v j))
abbrev direction (Q:znc jo) (i:rS) : (ChartRing Q i)[X] :=
 ayi Q i
abbrev TC (Q:znc jo) (i:rS) (a :ChartRing Q i) :=
 Localization.Away a
abbrev ap0 (Q:znc jo) (i:rS) (a :ChartRing Q i) :=
 dF ⊗[ao] TC Q i a
def avK (Q:znc jo) (i:rS) (a :ChartRing Q i) :
    (TC Q i a)[X] :=
  (direction Q i).map (algebraMap _ _)
def V5 (A:Type) [za6 A] [zZE ao A] :
    A[X] →+* dF ⊗[ao] A :=
  zqf Algebra.TensorProduct.includeRight.toRingHom
    (algebraMap dF _ PV)
abbrev SH {A:Type} [za6 A] (x :A) :=A ⧸ zye {x}
structure Factorization {A:Type} [za6 A] (f :A[X]) where
 n:ℕ
 factor :Fin n→ A[X]
 multiplicity :Fin n→ℕ
 product_eq :f = ∏ i,factor i^multiplicity i
 monic : ∀ i,(factor i).Monic
 multiplicity_bounds : ∀ i,0< multiplicity i∧multiplicity i≤133671
 pairwise_coprime :Pairwise (fun i j=>IsCoprime (factor i) (factor j))
 derivative_coprime : ∀ i,IsCoprime (factor i) (factor i).derivative
def auF {A:Type} [za6 A] {f :A[X]} (s :Factorization f) :A[X] :=
 ∏ i,s.factor i^(s.multiplicity i - 2)
def aFm {A:Type} [za6 A] {f :A[X]} (s :Factorization f) :A[X] :=
 ∏ i,s.factor i^min (s.multiplicity i) 2
def ab4 {A:Type} [za6 A] [zZE dF A] (d:Fin 3→A) :
    nW →ₐ[dF] A[X] :=
  zIe (fun j=>z1z (d j)*z7y)
def adu {A:Type} [za6 A] [zZE dF A] (d:Fin 3→A) :
    Ideal nW :=
  zdq (ab4 d).toRingHom
def adv {A:Type} [za6 A] [zZE dF A] (d:Fin 3→A)
    (L:Fin 2→nW) :l5 →ₐ[dF] A[X] :=
  (ab4 d).comp (zIe L)
def aj1 (F:Type) [zrb F] {A:Type} [za6 A] [zZE F A] (v w:A) :
    z3y (Fin 2) F →ₐ[F] A[X] :=
  zIe ![z1z v*z7y,z1z w*z7y]
abbrev biw {A:Type} [za6 A] [zZE dF A] (v w:A) :
  l5 →ₐ[dF] A[X] :=
 aj1 dF v w
abbrev aPb {A:Type} [za6 A] [zZE dF A]
  (φ:l5 →ₐ[dF] A) :Type :=
 letI:zeq l5 A:=zki A φ.toRingHom
 MY ⊗[l5] A
def azK {A:Type} [za6 A] [zZE dF A]
    (φ:l5 →ₐ[dF] A) :ℕ :=
  zsE MY (aPb φ)
end
end Pw
end
section
namespace Pw
noncomputable section
open aR B7 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 500000
private theorem arj {k E σ:Type} [zrb k] [za6 E] (α:k →+* E)
  (v :σ→E) (u:E) {p:z3y σ k} {n:ℕ} (h:p.IsHomogeneous n) :
  eval₂Hom α (fun j=>u*v j) p=u^n*eval₂Hom α v p:= by
 classical
 have hp:=(homogeneousComponent_eq_self h).symm.trans (homogeneousComponent_apply n p)
 rw [hp,map_sum,map_sum,zxw]
 apply zUo rfl
 intro d hd
 have hdeg:d.degree=n:=(Finset.mem_filter.mp hd).2
 simp only [eval₂Hom_monomial,zsa,mul_pow,zeY,
  zX0]
 change d.support.sum d=n at hdeg
 rw [hdeg]
 ac_rfl
private theorem dIw {k σ:Type} [zrb k] (Q:znc (z3y σ k))
    (hQ:Q.IsPrime) (hhom:Q.IsHomogeneous (homogeneousSubmodule σ k)) (i:σ)
    (hi:z9v i∉Q) :ztn (z3y σ k ⧸ (Q ⊔ zye {z9v i - 1})) := by
  classical
  let R:=z3y σ k ⧸ Q
  let:ztn R:=(zMn Q).2 hQ
  let E :=FractionRing R
  let q:z3y σ k →+* E :=(algebraMap R E).comp (zVv Q)
  let α:k →+* E :=q.comp C
  let z (j:σ) :=q (z9v j)
  let u:=z i
  have hu:u≠0:= by
    intro h
    apply hi
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply zxb R E
    change u=algebraMap R E 0
    rw [h,map_zero]
  let v (j:σ) :=z j/u
  let ψ:=eval₂Hom α v
  have hz :eval₂Hom α z=q:= by
    apply zXT
    · intro x
      simp [α]
    · simp [z]
  have hscale (p:z3y σ k) (n:ℕ) (hp:p.IsHomogeneous n) :
      q p=u^n*ψ p:= by
    have hv : (fun j=>u*v j)=z := by
      funext j
      exact mul_div_cancel₀ _ hu
    simpa only [ψ,hv,hz] using arj α v u hp
  let I:znc (z3y σ k) := Q ⊔ zye {z9v i - 1}
  have hI:I=zdq ψ:= by
    apply le_antisymm
    · refine sup_le (fun p hp => ?_) (Ideal.span_le.mpr ?_)
      · change ψ p=0
        rw [← sum_homogeneousComponent p,map_sum]
        apply zYF
        intro n _
        have hm:homogeneousComponent n p∈Q:=homogeneousComponent_mem_of_mem hhom hp n
        have hq:q (homogeneousComponent n p)=0:= by
          simp [q,Ideal.Quotient.eq_zero_iff_mem.mpr hm]
        rw [hscale _ _ (homogeneousComponent_isHomogeneous _ _)] at hq
        exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ hu)
      · intro p hp
        obtain rfl :=Set.mem_singleton_iff.mp hp
        change ψ (z9v i - 1)=0
        rw [map_sub,map_one,sub_eq_zero]
        simpa only [ψ,eval₂Hom_X',v] using div_self hu
    · intro p hp
      change ψ p=0 at hp
      let m:=p.totalDegree
      let H := ∑ n∈z4x (m+1),z9v i^(m - n)*homogeneousComponent n p
      have hqH :q H=u^m*ψ p:= by
        calc
          q H = ∑ n∈z4x (m+1),u^(m - n)*q (homogeneousComponent n p) := by
            simp only [H,map_sum,map_mul,map_pow,u,z]
          _ = ∑ n∈z4x (m+1),u^m*ψ (homogeneousComponent n p) := by
            apply zUo rfl
            intro n hn
            rw [hscale _ _ (homogeneousComponent_isHomogeneous _ _),← mul_assoc,← pow_add,
              zxt (zeh (Finset.mem_range.mp hn))]
          _=u^m*ψ p:= by
            rw [← zxw,← map_sum,sum_homogeneousComponent]
      have hH :H∈Q:= by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        apply zxb R E
        change q H=algebraMap R E 0
        rw [hqH,hp,mul_zero,map_zero]
      let π:=zVv I
      have hπ:π (z9v i)=1 :=sub_eq_zero.mp (by
        rw [← map_one π,← map_sub]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          ((show zye {z9v i - 1} ≤ I from le_sup_right)
            (z5J (z9v i - 1))))
      have hπH :π H=π p:= by
        calc
          π H = ∑ n∈z4x (m+1),π (homogeneousComponent n p) := by
            simp only [H,map_sum,map_mul,map_pow,hπ,one_pow,one_mul]
          _=π p:= by rw [← map_sum,sum_homogeneousComponent]
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (hπH ▸ Ideal.Quotient.eq_zero_iff_mem.mpr ((show Q≤I from le_sup_left) hH))
  exact (zMn I).2 (hI.symm ▸ zgL ψ)
private theorem d37 {k σ:Type} [zrb k] [Finite σ]
   (Q:znc (z3y σ k)) (hdim: (affineHilbertPolynomial Q).natDegree≠0) :
   ∃ i:σ,z9v i∉Q:= by
 by_contra! hall
 let q:=zVv Q
 have hmaps :q=q.comp (C.comp (eval (0:σ→k))) := by
   apply zXT
   · intro c
     simp
   · intro i
     simp only [zQb,eval_X,Pi.zero_apply,map_zero]
     exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i)
 have hsurj:zpX (algebraMap k (z3y σ k ⧸ Q)) := by
   intro a
   obtain ⟨p,rfl⟩:=zld a
   exact ⟨eval (0:σ→k) p,(zmU hmaps p).symm⟩
 let:zAa k (z3y σ k ⧸ Q) :=
   zIV (Algebra.linearMap k _) hsurj
 exact hdim (by rw [affineHilbertPolynomial_eq_C_finrank,zti])
private theorem c0K {k :Type} [zrb k] {n:ℕ}
    (Q:znc (z3y (Fin n) k)) (hQ:Q.IsPrime)
    (hhom:Q.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    (hdim: (affineHilbertPolynomial Q).natDegree≠0) :
    ∃ i:Fin n,z9v i∉Q∧ztn (yI Q i) ∧
      (ayi Q i).Monic∧(ayi Q i).natDegree≤ i.val := by
  classical
  let s :Finset (Fin n) :=Finset.univ.filter (fun i=>z9v i∉Q)
  obtain ⟨j,hj⟩:=d37 Q hdim
  obtain ⟨i,hi,hmax⟩:=Finset.exists_max_image s Fin.val ⟨j,by simp [s,hj]⟩
  have hiQ:z9v i∉Q:=(Finset.mem_filter.mp hi).2
  let I:znc (z3y (Fin n) k) := Q ⊔ zye {z9v i - 1}
  let q:=zVv I
  let hdom:=dIw Q hQ hhom i hiQ
  have :ztn (yI Q i) :=hdom
  have hqi:q (z9v i)=1 :=sub_eq_zero.mp (by
    rw [← map_one q,← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show zye {z9v i - 1} ≤ I from le_sup_right)
        (z5J (z9v i - 1))))
  have hcoeffi: (ayi Q i).coeff i.val=1 := by
    rw [ayi,zaW,zi6 i]
    · simpa only [z2j] using hqi
    · intro l _ hli
      simp [zQm,Fin.val_ne_of_ne hli]
    · simp
  have hle : (ayi Q i).natDegree≤ i.val := by
    unfold ayi
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro l _
    by_cases hl:l.val≤ i.val
    · exact Polynomial.natDegree_monomial_le _ |>.trans hl
    · have hlQ:z9v l∈Q:= by
        by_contra h
        exact hl (hmax l (by simp [s,h]))
      have hqQl:q (z9v l)=0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ((show Q≤I from le_sup_left) hlQ)
      change (zdM l.val (q (z9v l))).natDegree≤ i.val
      simp [hqQl]
  have hn: (ayi Q i).natDegree=i.val :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeffi]; exact one_ne_zero)
  exact ⟨i,hiQ,hdom,by rw [Polynomial.Monic,z4w,hn,hcoeffi],hle⟩
end
end Pw
end
section
namespace Pw
noncomputable section
open B7 Ey
open scoped Polynomial TensorProduct nonZeroDivisors
set_option maxHeartbeats 1000000
private theorem fVc {F A:Type} [zrb F] [za6 A] [zZE F A]
    (v w:A) (p:z3y (Fin 2) F) :
    (aj1 F v w p).map (zVv (zye {v})) =
      (((zpe F (Fin 1))
        ((z8s F 1 p).coeff 0)).map
          (algebraMap F (SH v))).comp
        (z1z (zVv (zye {v}) w)*z7y) := by
  let D:=SH v
  let ρ:A →+* D:=zVv (zye {v})
  let E :z3y (Fin 1) F →+* D[X] :=
    zOD (Polynomial.C.comp (algebraMap F D))
      (fun _=>z1z (ρ w)*z7y)
  have hv :ρ v=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (z5J v)
  have h :
      (zhd ρ).comp (aj1 F v w).toRingHom =
        (E.comp Polynomial.constantCoeff).comp (z8s F 1).toRingHom:= by
    apply zXT
    · intro c
      simp [aj1,E,MvPolynomial.finSuccEquiv_apply,zpj,ρ]
      rfl
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [aj1,E,MvPolynomial.finSuccEquiv_X_zero,hv,ρ]
      · change (aj1 F v w (z9v j.succ)).map ρ =
          E ((z8s F 1 (z9v j.succ)).coeff 0)
        rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.coeff_C_zero]
        fin_cases j
        simp [aj1,E]
  have hp:=zmU h p
  change _=E ((z8s F 1 p).coeff 0) at hp
  change ((zhd ρ).comp (aj1 F v w).toRingHom) p= _
  rw [hp]
  change MvPolynomial.eval₂ _ (fun _:Fin 1=>_) _ = _
  rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
  exact (zem _ _ _).symm
private theorem eLl {F A:Type} [zrb F] [za6 A] [ztn A]
    [zZE F A] (v w:A)
    (hw:IsUnit (zVv (zye {v}) w))
    (hinj:zq4 (aj1 F v w))
    [zAa F (SH v)] :
    let P:=z3y (Fin 2) F
    let K:=FractionRing P
    letI:zeq P A[X] :=zki A[X] (aj1 F v w).toRingHom
    zAa K (K ⊗[P] A[X]) →
      zsE F (SH v)≤zsE K (K ⊗[P] A[X]) := by
  classical
  intro P K hfin
  let D:=SH v
  let φ:=aj1 F v w
  let:zeq P A[X] :=zki A[X] φ.toRingHom
  let ρ:A →+* D:=zVv (zye {v})
  let view:=z8s F 1
  let read:=zpe F (Fin 1)
  let B:=Module.finBasis F D
  let r :=zsE F D
  choose lift hlift using fun i:Fin r=>zld (B i)
  have hli:z14 P (fun i:Fin r=>z1z (lift i)) := by
    rw [Fintype.linearIndependent_iff]
    intro p hp j
    change ∑ i,φ (p i)*z1z (lift i)=0 at hp
    by_contra hpj
    have he : ∃ n:ℕ,∃ i,(view (p i)).coeff n≠0:= by
      by_contra! h
      apply hpj
      exact view.injective (Polynomial.ext (fun n=> by simpa using h n j))
    let n:=Nat.find he
    have hdiv (i) :z7y ^n∣view (p i) :=
      Polynomial.X_pow_dvd_iff.mpr (fun k hk=> by
        by_contra hc
        exact (Nat.find_min he hk) ⟨i,hc⟩)
    choose q hq using hdiv
    let a :Fin r→P:= fun i=>view.symm (q i)
    have hx :view.symm (z7y: (z3y (Fin 1) F)[X])=z9v 0 :=
      view.symm_apply_eq.mpr (MvPolynomial.finSuccEquiv_X_zero.symm)
    have hpa (i) :p i=z9v 0^n*a i:= by
      have heq :=congrArg (fun p=>view.symm p) (hq i)
      change view.symm (view (p i))=view.symm (z7y ^n*q i) at heq
      rw [AlgEquiv.symm_apply_apply,map_mul,map_pow,hx] at heq
      exact heq
    have ha : ∑ i,φ (a i)*z1z (lift i)=0:= by
      have hz : (φ (z9v 0)^n)≠0:= by
        apply pow_ne_zero
        intro hx₀
        exact MvPolynomial.X_ne_zero 0 (hinj (hx₀.trans (map_zero φ).symm))
      rw [show (∑ i,φ (p i)*z1z (lift i)) =
          φ (z9v 0)^n * ∑ i,φ (a i)*z1z (lift i) by
        rw [zxw]
        apply zUo rfl
        intro i _
        rw [hpa i,map_mul,map_pow,mul_assoc]] at hp
      exact (mul_eq_zero.mp hp).resolve_left hz
    have hred:=congrArg (zhd ρ) ha
    have hb (i) :ρ (lift i)=B i:=hlift i
    have hmap (i:Fin r) : ((aj1 F v w) (a i)).map ρ =
        ((read ((view (a i)).coeff 0)).map (algebraMap F D)).comp
          (z1z (ρ w)*z7y) :=
      fVc v w (a i)
    simp only [φ,map_sum,map_mul,map_zero,zKC,zrL,
      hmap,hb] at hred
    have hc (k :ℕ) : ∀ i,(read ((view (a i)).coeff 0)).coeff k=0:= by
      apply Fintype.linearIndependent_iff.mp B.linearIndependent
      have hcoeff :=congrArg (fun f :D[X]=>f.coeff k) hred
      simp only [zaW,Polynomial.coeff_mul_C,Polynomial.comp_C_mul_X_coeff,
        z0b,zO6] at hcoeff
      apply (hw.pow k).mul_right_inj.mp
      rw [mul_zero,zxw]
      convert hcoeff using 1
      apply zUo rfl
      intro i _
      rw [zd5]
      ring
    obtain ⟨i,hi⟩:=Nat.find_spec he
    apply hi
    have hcoef : (view (p i)).coeff n=(q i).coeff 0:= by
      rw [hq i]
      simpa using zxk (q i) n 0
    rw [hcoef]
    apply read.injective
    apply Polynomial.ext
    intro k
    simpa only [map_zero,zO6,a,AlgEquiv.apply_symm_apply] using hc k i
  have hLI:=hli.of_isLocalizedModule K (nonZeroDivisors P) (zUP P K A[X] 1)
  simpa only [zgY] using hLI.fintype_card_le_finrank
theorem eLk {A:Type} [za6 A] [ztn A] [zZE dF A] (v w:A)
  (hw:IsUnit (zVv (zye {v}) w))
  (hinj:zq4 (biw v w))
  [hfin:zAa MY (aPb (biw v w))]
  [zAa dF (SH v)] :
  zsE dF (SH v)≤azK (biw v w) :=
 eLl (F:=dF) v w hw hinj hfin
end
end Pw
end
section
namespace Pw
noncomputable section
open B7
set_option backward.isDefEq.respectTransparency false
private theorem cSf {A:Type} [za6 A] [ztn A]
    [zZE dF A] (I:znc A) (hI:I.IsPrincipal) (hne :I ≠ ⊥)
    [zAa dF (A ⧸ I)] (n:ℕ) :
    zAa dF (A ⧸ I ^n) ∧
      zsE dF (A ⧸ I ^n)=n*zsE dF (A ⧸ I) := by
  have hrank : ∀ n:ℕ,z1x dF (A ⧸ I ^n) =
      n•z1x dF (A ⧸ I) := by
    intro m
    induction m with
    | zero =>
      have :zOt (A ⧸ I ^0) :=Ideal.Quotient.subsingleton_iff.mpr (by simp)
      simp
    | succ m ih =>
      let J:znc A:=I ^(m+1)
      let S:=(I ^m).map (zVv J)
      have hJI:J≤I ^m:=Ideal.pow_le_pow_right (zqk m)
      let e₁: ((A ⧸ J) ⧸ S) ≃ₐ[dF] (A ⧸ I ^m) :=
        DoubleQuot.quotQuotEquivQuotOfLEₐ dF hJI
      let e₂: (A ⧸ I) ≃ₗ[dF] S :=
        ((Ideal.quotEquivPowQuotPowSucc hI hne m).trans
          (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I m)).restrictScalars dF
      have h:=Submodule.rank_quotient_add_rank (S.restrictScalars dF)
      change z1x dF ((A ⧸ J) ⧸ S)+Module.rank dF S =
        z1x dF (A ⧸ I ^(m+1)) at h
      rw [e₁.toLinearEquiv.rank_eq,← e₂.rank_eq,ih] at h
      simpa only [succ_nsmul] using h.symm
  refine ⟨Module.rank_lt_aleph0_iff.mp ?_,?_⟩
  · rw [hrank,Cardinal.nsmul_lt_aleph0_iff]
    exact Or.inr (Module.rank_lt_aleph0 _ _)
  · simpa only [zsE,nsmul_eq_mul,Cardinal.toNat_mul,Cardinal.toNat_natCast] using
      congrArg Cardinal.toNat (hrank n)
theorem evE {A:Type} [za6 A] [ztn A] [zZE dF A]
    (x y :A) (N :ℕ) (hx :x≠0) (hy :y≠0) (hxy :y∣x) (hpow:x^2∣y ^N)
    [zAa dF (SH x)] :
    zAa dF (SH y) ∧
      2*zsE dF (SH x) ≤
        N*zsE dF (SH y) := by
  let I:znc A:=zye {x}
  let J:znc A:=zye {y}
  have hIJ:I≤J:=Ideal.span_singleton_le_span_singleton.mpr hxy
  let f :=(z5F dF hIJ).toLinearMap
  have :zAa dF (SH y) :=
    zIV f (zuo hIJ)
  refine ⟨inferInstance,?_⟩
  obtain ⟨_,hxlen⟩:=cSf I (by infer_instance)
    (by simpa only [I,ne_eq,Ideal.span_singleton_eq_bot] using hx) 2
  obtain ⟨hyfin,hylen⟩:=cSf J (by infer_instance)
    (by simpa only [J,ne_eq,Ideal.span_singleton_eq_bot] using hy) N
  have hpowIJ:J^N≤I ^2 := by
    dsimp only [I,J]
    rw [zNi,zNi]
    exact Ideal.span_singleton_le_span_singleton.mpr hpow
  let g:=(z5F dF hpowIJ).toLinearMap
  have hle :=LinearMap.finrank_le_finrank_of_surjective (f :=g)
    (zuo hpowIJ)
  rwa [hxlen,hylen] at hle
end
end Pw
end
section
namespace bz0
noncomputable section
open cu gT DQ Cu UI XW
open aiN
open scoped Polynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:znc kM} {g n:ℕ}
 {R:wJ C₀ J g} (A:yI R n)
def pD:DT n →+* oO C₀ :=
 zOD (zT C₀) A.coordinate
instance : (TU A).IsPrime :=zgL (pD A)
abbrev jo:=DT n ⧸ TU A
abbrev aao:=FractionRing (jo A)
def apG:DT n →+* aao A :=
 (algebraMap (jo A) (aao A)).comp (zVv _)
private def c53:jo A →+* oO C₀ :=
 RingHom.kerLift (pD A)
def aq0:aao A →+* oO C₀ :=
 zIj (g:=c53 A) (zuJ (pD A))
@[simp] theorem cF2 (q:DT n) :
   aq0 A (apG A q)=pD A q :=
  zoc (g:=c53 A)
   (zuJ (pD A)) _
def KK:FX:=algebraMap L[X] FX z7y
theorem b2z :Mr C₀ KK=F5 C₀ Polynomial.X:= by
 unfold Mr KK zJ1
 rw [zi7]
 simp [F5]
theorem bpV (a :L) :
  Mr C₀ (algebraMap L FX a)=Mu C₀ (zT C₀ a) := by
 rw [zG3 L L[X] FX]
 unfold Mr zJ1
 rw [zi7]
 simp [Mu,F5]
def bXX (i:Fin n) :akF A:= by
  letI:zZE FX (EC R) :=(amB R).toAlgebra
  exact ⟨LW R (A.coordinate i),IntermediateField.subset_adjoin FX _
    (zt3 _ (zWL i))⟩
def arT:DT n →+* akF A :=
 zOD ((aq1 A).comp (algebraMap L FX)) (bXX A)
theorem c3z :
   (auC A).comp (arT A) =
     (LW R).comp (pD A) := by
 apply zXT
 · intro a
   simp only [arT,pD,zTv,zQb]
   change AdjoinRoot.of _ (Mr C₀ (algebraMap L FX a)) =
     AdjoinRoot.of _ (Mu C₀ (zT C₀ a))
   rw [bpV]
 · intro i
   simp only [arT,pD,zrD,zQb]
   rfl
theorem cbl:zdq (arT A)=TU A:= by
 ext q
 rw [RingHom.mem_ker]
 change arT A q=0↔pD A q=0
 rw [← (auC A).injective.eq_iff,map_zero,
  ← zQb,c3z,zQb,
  ← (LW R).injective.eq_iff,map_zero]
private def c51 :jo A →+* akF A :=
 zP2 _ (arT A)
  (fun _ h=>RingHom.mem_ker.mp ((cbl A).symm ▸ h))
private theorem c52 :zq4 (c51 A) := by
 intro a b h
 obtain ⟨a,rfl⟩:=zld a
 obtain ⟨b,rfl⟩:=zld b
 apply Ideal.Quotient.eq.mpr
 rw [← cbl A,RingHom.mem_ker,map_sub,sub_eq_zero]
 exact h
def aCG:aao A →+* akF A :=
 zIj (c52 A)
@[simp] theorem bXF (q:DT n) :
   aCG A (apG A q)=arT A q :=
  zoc (g:=c51 A) (c52 A) _
theorem dMg :
  (auC A).comp (aCG A)=(LW R).comp (aq0 A) := by
 apply z2O (A:=jo A)
 intro a
 obtain ⟨q,rfl⟩:=zld a
 change auC A (aCG A (apG A q)) =
  LW R (aq0 A (apG A q))
 rw [bXF,cF2]
 exact zLs (c3z A) q
abbrev a9Y:=((aao A)[X])[X]
def aI7:a9Y A :=
 A.equation.map (zhd (apG A))
def amu:a9Y A →+* akF A :=
  zqf (zqf (aCG A) (aq1 A KK))
    (bcB A)
private theorem cMA :
   (aI7 A).map (zhd (aq0 A)) =
     z1z (z1z (A.scale :oO C₀))*R.equation := by
 rw [aI7,zoi,Polynomial.mapRingHom_comp,← A.generic_eq]
 congr 2
 exact zz4 (cF2 A)
theorem bpv : (aI7 A).IsPrimitive := by
 let i:=zhd (aq0 A)
 have hprim: ((aI7 A).map i).IsPrimitive := by
   rw [show i=zhd (aq0 A) from rfl,cMA]
   exact Polynomial.isPrimitive_of_dvd R.primitive
     (associated_unit_mul_left _ _ (A.scale.isUnit.map (Polynomial.C.comp z1z))).dvd
 refine Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr fun d hd => ?_
 have hm:IsUnit (i d) :=
   Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim _ (by simpa using map_dvd (zhd i) hd)
 rw [Polynomial.isUnit_iff_degree_eq_zero] at hm ⊢
 simpa only [i,zKC,Polynomial.degree_map_eq_of_injective
   (aq0 A).injective] using hm
private def bcx :FractionRing (aao A)[X] →+* y7 C₀ :=
 zJ1 (j:=zhd (aq0 A))
  (zTo _ (aq0 A).injective)
private theorem cF4 (a : (aao A)[X]) :
   bcx A (algebraMap _ (FractionRing (aao A)[X]) a) =
     F5 C₀ (a.map (aq0 A)) := by
 unfold bcx zJ1
 rw [zi7]
 rfl
private abbrev ve :=
 (aI7 A).map (algebraMap (aao A)[X] (FractionRing (aao A)[X]))
private theorem efv :
   (ve A).map (bcx A) =
     z1z (Mu C₀ (A.scale :oO C₀))*K8 R:= by
 rw [zoi,show (bcx A).comp
   (algebraMap (aao A)[X] (FractionRing (aao A)[X])) =
     (F5 C₀).comp (zhd (aq0 A)) from
   zz4 (cF4 A),← zoi,
   cMA,zNl,zrL]
 rfl
private theorem fTU :
    (auC A).comp (amu A) =
      (AdjoinRoot.mk (K8 R)).comp
        (zhd ((F5 C₀).comp (zhd (aq0 A)))) := by
  apply z86
  · have h: (auC A).comp
        (zqf (aCG A) (aq1 A KK)) =
      (AdjoinRoot.of (K8 R)).comp
        ((F5 C₀).comp (zhd (aq0 A))) := by
      apply z86
      · intro a
        simp only [zQb,z4Q,zJU,
          zKC,zrL]
        exact zLs (dMg A) a
      · simp only [zQb,z4Q,zC9,
          zKC,zSo]
        exact congrArg (AdjoinRoot.of (K8 R)) (b2z (C₀:=C₀))
    intro a
    simpa only [amu,zQb,z4Q,zJU,
      zKC,zrL,AdjoinRoot.of] using zLs h a
  · simp only [amu,zQb,z4Q,zC9,
      zKC,zSo,AdjoinRoot.mk_X]
    rfl
theorem c62 (q:a9Y A) :
    amu A q=0↔aI7 A∣q:= by
  let k :=algebraMap (aao A)[X] (FractionRing (aao A)[X])
  rw [← (auC A).injective.eq_iff,map_zero,← zQb,
    fTU,zQb,zKC,
    ← show (q.map k).map (bcx A) =
      q.map ((F5 C₀).comp (zhd (aq0 A))) by
        rw [zoi]
        congr 1
        exact zz4 (cF4 A)]
  rw [AdjoinRoot.mk_eq_zero]
  have ha :Associated ((ve A).map (bcx A)) (K8 R) := by
    rw [efv]
    exact associated_unit_mul_left _ _ (A.scale.isUnit.map (Polynomial.C.comp (Mu C₀)))
  rw [← ha.dvd_iff_dvd_left,Polynomial.map_dvd_map']
  exact (Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map
    (FractionRing (aao A)[X]) (bpv A)).symm
end
end bz0
end
section
namespace Pw
noncomputable section
open aR B7 Ey
open scoped Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
def c1 :Prop :=
  ∀ (Q:znc jo) (i:rS) (a :ChartRing Q i),
    Q.IsPrime→Q.IsHomogeneous (zbm rS ao) →
    (zIU Q).natDegree=2 →
    z9v i∉Q→ ztn (ChartRing Q i)→a≠0 →
    ztn (ap0 Q i a) ∧
    zq4 (V5 (TC Q i a)) ∧
    zAa dF (SH (V5 _ (avK Q i a))) ∧
    (zsE dF
      (SH (V5 _ (avK Q i a))) :ℚ)=MvPolynomial.affineDegree Q
def c2 :Prop :=
  ∀ (A:Type) [za6 A] [ztn A] [zZE ao A] (f :A[X]),
    f.Monic→f.natDegree≤133671 →
    ∃ (a :A),a≠0∧Nonempty (Factorization (f.map (algebraMap A (Localization.Away a))))
def c3:Prop :=
  ∀ (A:Type) [za6 A] [zZE ao A] (f :A[X]) (s :Factorization f),
    ∃ q:Fin 3→ A[X],q 0=aFm s ∧
      (∀ j,auF s*q j=z75 j.val f) ∧
      zye (zxp q) = ⊤
def c4 :Prop :=
  ∀ (Q:znc jo) (i:rS) (a :ChartRing Q i),
    Q.IsPrime→Q.IsHomogeneous (zbm rS ao) →
    (zIU Q).natDegree=2 →
    z9v i∉Q→ ztn (ChartRing Q i)→a≠0 →
    ztn (ap0 Q i a) →
    ∀ (b:ap0 Q i a) (d:Fin 3→ap0 Q i a),b≠0 →
      (∀ j,b*d j=V5 _ (z75 j.val (avK Q i a))) →
      aVq (oV Q)=adu d ∧
      ∀ L,agE L (aVq (oV Q)) →
        zAa MY (aPb (adv d L)) ∧
        azK (adv d L)=adI L (oV Q)
def c5:Prop :=
  ∀ (A:Type) [za6 A] [ztn A] [zZE dF A]
    (d:Fin 3→A) (L:Fin 2→nW),
    d 0≠0 → ¬ IsUnit (d 0)→ zye (zxp d) = ⊤ →
    agE L (adu d) →
    ∃ (M:Fin 2→nW) (w:A),agE M (adu d) ∧
      adv d M=biw (d 0) w ∧
      zq4 (adv d M) ∧
      IsUnit (zVv (zye {d 0}) w)
def c6:Prop :=
  ∀ (A:Type) [za6 A] [ztn A] [zZE dF A]
    (d:Fin 3→A) (L M:Fin 2→nW),
    agE L (adu d)→zAa MY (aPb (adv d L)) →
    agE M (adu d)→zq4 (adv d M) →
    zAa MY (aPb (adv d M)) ∧
      azK (adv d M)=azK (adv d L)
private theorem cG8 {A:Type} [za6 A] {f :A[X]}
  (s :Factorization f) : (auF s).Monic :=
 zRn _ _ (fun i _=>(s.monic i).pow _)
private theorem dh5 {A:Type} [za6 A] {f :A[X]}
  (s :Factorization f) : (aFm s).Monic :=
 zRn _ _ (fun i _=>(s.monic i).pow _)
private theorem dh4 {A:Type} [za6 A] {f :A[X]}
  (s :Factorization f) :aFm s∣f := by
 exact (Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>pow_dvd_pow _ (min_le_left _ _))).trans
  (dvd_of_eq s.product_eq.symm)
end
end Pw
end
section
set_option maxHeartbeats 1200000
namespace aA7
noncomputable section
open aR dN rW MJ MvPolynomial
open scoped TensorProduct
variable {k E σ ι:Type*} [zrb k] [zrb E] [zZE k E]
private abbrev uZ:z3y σ k →+* z3y σ E :=
 zDK (algebraMap k E)
private def Pd (I:znc (z3y σ k)) :
  E ⊗[k] (z3y σ k ⧸ I) ≃ₐ[E] z3y σ E ⧸ I.map uZ:= by
 let e :=zoR (σ:=σ) k E
 let ι' : z3y σ k →ₐ[k] E ⊗[k] z3y σ k :=
  zgi
 have hcomp:e.toRingHom.comp ι'.toRingHom=uZ:= by
  apply zz4
  intro p
  change e (1 ⊗ₜ[k] p)= _
  simp [e,uZ]
 refine (zTd (R:=k) E _ E I).trans
  (zpY _ _ e ?_)
 exact ((z0L (I:=I) ι'.toRingHom e.toRingHom).trans
  (congrArg (fun f=>I.map f) hcomp)).symm
private theorem aWG (I:znc (z3y σ k))
  (a :E) (p:z3y σ k) :
  Pd I (a ⊗ₜ[k] zVv I p) =
    zVv (I.map uZ) (zoR k E (a ⊗ₜ[k] p)) := by
 simp only [Pd,AlgEquiv.trans_apply,zTe]
 rfl
private def dO [DecidableEq ι] (b:z39 ι k E) (p:z3y σ E) (i:ι) :
  z3y σ k :=
 znu b ((zoR k E).symm p) i
private theorem bnn [DecidableEq ι] (b:z39 ι k E) (p:z3y σ E)
   (i:ι) (d:σ →₀ ℕ) : (dO b p i).coeff d=b.coord i (p.coeff d) := by
 let e :=zoR (σ:=σ) k E
 obtain ⟨t,rfl⟩:=e.surjective p
 simp only [dO,show zoR k E=e from rfl,
   AlgEquiv.symm_apply_apply]
 induction t using z2P with
 | tmul a q =>
   simp only [zy4,e,
     algebraTensorAlgEquiv_tmul,coeff_smul,coeff_map]
   have hs :a•algebraMap k E (q.coeff d)=q.coeff d•a := by
     rw [smul_eq_mul,zd5,mul_comm]
   simp only [hs,map_smul,zVi,smul_eq_mul,mul_comm]
 | add t u ht hu =>
   simp only [map_add,AddMonoidAlgebra.coeff_add,zSs,ht,hu]
private theorem mem_map_iff [DecidableEq ι] (b:z39 ι k E)
    (I:znc (z3y σ k)) (p:z3y σ E) :
    p∈I.map uZ ↔ ∀ i,dO b p i∈I:= by
  let e :=zoR (σ:=σ) k E
  let eI:E ⊗[k] (z3y σ k ⧸ I) ≃ₐ[E] _:=Pd I
  let s :=znu (N :=z3y σ k ⧸ I) b
  obtain ⟨t,rfl⟩:=e.surjective p
  have hc (i:ι) :
      s (eI.symm (zVv (I.map uZ) (e t))) i =
        zVv I (znu b t i) := by
    induction t using z2P with
    | tmul a q =>
      rw [← aWG I a q]
      simp only [eI,AlgEquiv.symm_apply_apply,s,
        zy4]
      exact (map_smul (zvR k I) _ _).symm
    | add t u ht hu =>
      simp only [map_add,zSs,ht,hu]
  simp only [dO,show zoR k E=e from rfl,
    AlgEquiv.symm_apply_apply,← z1Q,← hc]
  constructor
  · intro h i
    simp [h]
  · intro h
    have hz :s (eI.symm (zVv (I.map uZ) (e t)))=0 :=
      Finsupp.ext h
    exact eI.symm.injective (s.injective (hz.trans (by simp)))
private theorem bdo [DecidableEq ι] (b:z39 ι k E) (p:z3y σ E)
    (i:ι) (x :σ→k) :
    eval x (dO b p i)=b.coord i (eval ((algebraMap k E) ∘ x) p) := by
  let e :=zoR (σ:=σ) k E
  obtain ⟨t,rfl⟩:=e.surjective p
  simp only [dO,show zoR k E=e from rfl,
    AlgEquiv.symm_apply_apply]
  induction t using z2P with
  | tmul a q =>
    simp only [zy4,e,
      algebraTensorAlgEquiv_tmul,← aeval_eq_eval,map_smul]
    have he :eval ((algebraMap k E) ∘ x) (uZ q)=algebraMap k E (eval x q) := by
      simpa only [uZ,eval_map,RingHom.comp_id,eval₂_id] using
        (eval₂_comp_left (algebraMap k E) (zz5 k) x q).symm
    rw [show zDK (algebraMap k E) q=uZ q from rfl]
    simp only [aeval_eq_eval,he]
    have hs :a•algebraMap k E (eval x q)=eval x q•a := by
      rw [smul_eq_mul,zd5,mul_comm]
    simp only [hs,map_smul,zVi,smul_eq_mul,mul_comm]
  | add t u ht hu =>
    simp only [map_add,zSs,ht,hu]
private theorem bcK (I:znc (z3y σ k)) {p:z3y σ k}
   (hp:p∈I) {n:ℕ} (hn:p.totalDegree≤n) :
   homogeneousComponent n p∈lW I:= by
 rcases eq_or_lt_of_le hn with rfl | hlt
 · exact zCn ⟨p,hp,rfl⟩
 · rw [homogeneousComponent_eq_zero n p hlt]
   exact znl _
private theorem bmp (I:znc (z3y σ k)) :
    lW (I.map (uZ (E :=E)))=(lW I).map uZ:= by
  classical
  let b:=zz1 k E
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    apply (mem_map_iff b _ _).2
    intro i
    have hi:=(mem_map_iff b I p).1 hp i
    have hn: (dO b p i).totalDegree≤p.totalDegree := by
      apply zRS
      intro d hd
      rw [zuk,bnn] at hd
      exact MvPolynomial.mem_support_iff.mpr fun h=>hd (by rw [h,map_zero])
    have he :dO b (homogeneousComponent p.totalDegree p) i =
        homogeneousComponent p.totalDegree (dO b p i) := by
      ext d
      by_cases hd:d.degree=p.totalDegree <;>
        simp [bnn,coeff_homogeneousComponent,hd]
    rw [he]
    exact bcK I hi hn
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    change uZ (homogeneousComponent p.totalDegree p)∈lW _
    have he :uZ (homogeneousComponent p.totalDegree p) =
        homogeneousComponent p.totalDegree (uZ (E :=E) p) := by
      ext d
      by_cases hd:d.degree=p.totalDegree <;>
        simp only [uZ,coeff_map,coeff_homogeneousComponent,hd,ite_true,ite_false,
          map_zero]
    rw [he]
    exact bcK _ (z7X _ hp)
      (zRS (support_map_subset (algebraMap k E) p))
private theorem c0b [Finite σ] [IsAlgClosed k]
   (I:znc (z3y σ k)) [I.IsPrime] (p:z3y σ E) :
   p∈I.map uZ ↔
     ∀ x∈zeroLocus k I,eval ((algebraMap k E) ∘ x) p=0:= by
 classical
 let b:=zz1 k E
 rw [mem_map_iff b]
 constructor
 · intro h x hx
   apply b.forall_coord_eq_zero_iff.mp
   intro i
   rw [← bdo]
   exact hx _ (h i)
 · intro h i
   rw [← IsPrime.vanishingIdeal_zeroLocus (K:=k) I]
   intro x hx
   change eval x (dO b p i)=0
   rw [bdo,h x hx,map_zero]
theorem beK [Finite σ] [IsAlgClosed k]
   (I:znc (z3y σ k)) (hI:I.IsPrime) :
   (I.map (zDK (algebraMap k E))).IsPrime := by
 classical
 let b:=zz1 k E
 apply Ideal.isPrime_iff.mpr
 constructor
 · intro htop
   have hz :=(c0b I (1 :z3y σ E)).mp (by simp [htop])
   apply hI.ne_top
   apply I.eq_top_of_isUnit_mem _ isUnit_one
   rw [← IsPrime.vanishingIdeal_zeroLocus (K:=k) I]
   intro x hx
   exact (one_ne_zero ((eval _).map_one.symm.trans (hz x hx))).elim
 · intro p q hpq
   by_cases hp:p∈I.map (uZ (E :=E))
   · exact Or.inl hp
   right
   apply (mem_map_iff b I q).mpr
   obtain ⟨i,hi⟩:=not_forall.mp fun h=>hp ((mem_map_iff b I p).mpr h)
   intro j
   apply (hI.mem_or_mem ?_).resolve_left hi
   rw [← IsPrime.vanishingIdeal_zeroLocus (K:=k) I]
   intro x hx
   have hz :=(c0b I (p*q)).mp hpq x hx
   rw [map_mul] at hz
   change eval x (dO b p i*dO b q j)=0
   rw [map_mul,bdo,bdo]
   rcases mul_eq_zero.mp hz with hz | hz <;> simp [hz]
theorem proof :MJ.c2 := by
 intro A _
 let:zZE ao GeoField:=ni.toAlgebra
 refine ⟨Ey.ZI (E :=GeoField) A,?_⟩
 intro P hP
 have hb:lW (gN A)=(lW A).map
     (uZ (k :=ao) (E :=GeoField)) :=bmp A
 have hle : (lW A).map (uZ (k :=ao) (E :=GeoField))≤P :=
   hb ▸ hP.le
 let: (P.comap (uZ (k :=ao) (E :=GeoField))).IsPrime :=
   hP.isPrime.comap _
 obtain ⟨R,hR,hRP⟩:=Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hle)
 have hRP' : gN R≤P:=Ideal.map_le_iff_le_comap.mpr hRP
 have hR' : (gN R).IsPrime :=beK R hR.isPrime
 exact ⟨R,hR,le_antisymm hRP' (hP.2 ⟨hR',hb.trans_le (Ideal.map_mono hR.le)⟩ hRP')⟩
end
end aA7
end
section
namespace aFR
noncomputable section
open aR B7 Pw
open scoped Polynomial
abbrev asz (R:Type) [za6 R] :R →+* FractionRing R :=
 algebraMap R (FractionRing R)
def bcm (Q:znc jo) (i:rS) (a :ChartRing Q i)
    (j:rS) :ap0 Q i a :=
  zgi (R:=ao)
    (algebraMap (ChartRing Q i) (TC Q i a)
      (zVv _ (z9v j)))
end
end aFR
end
section
namespace aFR
noncomputable section
open aR B7 Ey Pw
open scoped Polynomial TensorProduct nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
def c1 :Prop :=
  ∀ (Q:znc jo) (i:rS) (a :ChartRing Q i),
    Q.IsPrime→Q.IsHomogeneous (zbm rS ao) →
    z9v i∉Q→ ztn (ChartRing Q i)→a≠0 →
    ztn (ap0 Q i a) →
    ∃ e :FractionRing (mK ⧸ oV Q) ≃ₐ[dF]
        FractionRing ((ap0 Q i a)[X]),
      ∀ j:rS,
        e (asz (mK ⧸ oV Q)
          (zVv _ (z9v j))) =
        asz (ap0 Q i a)[X]
          (z1z (bcm Q i a j)*z7y)
def c2 :Prop :=
  ∀ (I:znc mK) [ztn (mK ⧸ I)]
    (A:Type) [za6 A] [ztn A] [zZE dF A]
    (φ:l5 →ₐ[dF] (mK ⧸ I)) (ψ:l5 →ₐ[dF] A)
    (e :FractionRing (mK ⧸ I) ≃ₐ[dF] FractionRing A),
    (zIU I).natDegree=2 →
    (∀ p,e (asz (mK ⧸ I) (φ p))=asz A (ψ p)) →
    zAa MY (aPb ψ)∧azK ψ=azK (A:=mK ⧸ I) φ
private theorem gl6 {F A:Type} [zrb F] [za6 A] [ztn A]
    [zZE F A] (b:A) (hb:b≠0) :
    ∃ e :FractionRing A[X] ≃ₐ[F] FractionRing A[X],∀ x :A,
      e (algebraMap A[X] _ (z1z x*z7y)) =
        algebraMap A[X] _ (z1z (b*x)*z7y) := by
  let E :=FractionRing A[X]
  let j:A[X] →ₐ[A] E :=zE2 A A[X] E
  let s :A[X] →ₐ[A] A[X] :=zEU (z1z b*z7y)
  have hs :zq4 s :=(injective_iff_map_eq_zero s).mpr (fun p hp =>
    (Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hb)).mp hp)
  have hinj:zq4 (j.comp s) :=(zxb A[X] E).comp hs
  let f :E →ₐ[A] E :=zeU (g:=j.comp s) hinj
  have hf (p:A[X]) :f (j p)=j (s p) :=zoc hinj p
  have hsC (x :A) :s (z1z x)=z1z x :=z8q _ _
  have hsX:s z7y=z1z b*Polynomial.X:=zw0 _
  let g:A[X] →ₐ[A] E :=zEU (j z7y/j (z1z b))
  have hg:f.comp g=j:= by
    apply Polynomial.algHom_ext
    change f (g z7y)=j z7y
    rw [show g z7y= _ from zw0 _,map_div₀,hf,hf,hsC,hsX,map_mul]
    apply mul_div_cancel_left₀
    intro hz
    apply (Polynomial.C_ne_zero.mpr hb:z1z b≠(0:A[X]))
    apply zxb A[X] E
    change j (z1z b)=j 0
    rw [hz,map_zero]
  have hsurj:zpX f := by
    intro z
    obtain ⟨u,v,_,rfl⟩:=zJC A[X] z
    refine ⟨g u/g v,?_⟩
    rw [map_div₀]
    exact congrArg₂ (· / ·) (zmU hg u) (zmU hg v)
  let e :=AlgEquiv.ofBijective f ⟨f.injective,hsurj⟩
  refine ⟨e.restrictScalars F,fun x => ?_⟩
  change f (j (z1z x*z7y))=j _
  rw [hf,map_mul,hsC,hsX,← mul_assoc,← Polynomial.C_mul,mul_comm x b]
private theorem d2q {ι A B F:Type} [z85 ι] [za6 A] [za6 B]
    [za6 F] (ρ:A →+* B) (γ:F →+* B) (x :F)
    (n:ι→ℕ) (v :ι→A) (j:ℕ) :
    zqf ρ (γ x)
        (z75 j (∑ l,zdM (n l) (v l))) =
      ∑ l,γ ((n l).choose j*x^(n l - j))*ρ (v l) := by
  simp only [map_sum]
  refine zUo rfl fun l _ => ?_
  rw [Polynomial.hasseDeriv_monomial]
  simp only [z4Q,zFK,map_mul,map_natCast,map_pow]
  ac_rfl
private theorem aHH {ι F B:Type} [z85 ι] [zrb F] [za6 B] [zZE F B]
  (v :ι→B) (w:ι→F) :
  zIe (fun l=>z1z (v l)*z7y)
    (∑ l,znf (w l)*z9v l) =
  z1z (∑ l,algebraMap F B (w l)*v l)*Polynomial.X:= by
 simp only [map_sum,map_mul,MvPolynomial.aeval_C,zTw,
  zpj,zkq]
 refine zUo rfl fun l _ => ?_
 ac_rfl
private theorem dMp (Q:znc jo) (i:rS) (a :ChartRing Q i)
    (j:Fin 3) :
    zIe (R:=dF)
      (fun l=>z1z (bcm Q i a l)*z7y) (KT PV j.val) =
    z1z (V5 _ (z75 j.val (avK Q i a))) *
      Polynomial.X:= by
  let v (l:rS) :TC Q i a :=
    algebraMap (ChartRing Q i) (TC Q i a) (zVv _ (z9v l))
  have hopen:avK Q i a = ∑ l:rS,zdM l.val (v l) := by
    simp only [avK,direction,ayi,Polynomial.map_sum,Polynomial.map_monomial,v]
  have heval :V5 _ (z75 j.val (avK Q i a)) =
      ∑ l:rS,algebraMap dF (ap0 Q i a)
        (l.val.choose j.val*PV^(l.val - j.val))*bcm Q i a l:= by
    rw [hopen]
    exact d2q Algebra.TensorProduct.includeRight.toRingHom
      (algebraMap dF (ap0 Q i a)) PV Fin.val v j.val
  rw [heval]
  exact aHH (bcm Q i a) (fun l=>l.val.choose j.val*PV^(l.val - j.val))
theorem of_children (h1 :c1) (h2 :c2) :Pw.c4 := by
  intro Q i a hQ hhom hdim hi hchart ha hopen b d hb htrim
  let R:=mK ⧸ oV Q
  let B:=ap0 Q i a
  let:ztn R:=(zMn _).mpr (bqp Q hQ)
  let:ztn B:=hopen
  let jR:R →ₐ[dF] FractionRing R:=zE2 dF R _
  let jB:B[X] →ₐ[dF] FractionRing B[X] :=zE2 dF B[X] _
  obtain ⟨e,he⟩:=h1 Q i a hQ hhom hi hchart ha hopen
  obtain ⟨s,hs⟩:=gl6 (F:=dF) b hb
  let q:mK →ₐ[dF] FractionRing R :=
    jR.comp (zvR dF (oV Q))
  let t:mK →ₐ[dF] B[X] :=
    zIe (fun j=>z1z (bcm Q i a j)*z7y)
  have heq :e.toAlgHom.comp q=jB.comp t:= by
    apply zpH
    intro j
    change e (jR (zVv (oV Q) (z9v j))) =
      jB (t (z9v j))
    rw [show t (z9v j)=z1z (bcm Q i a j)*z7y from
      zTw _ j]
    exact he j
  have hjet: (e.toAlgHom.comp q).comp tO =
      s.toAlgHom.comp (jB.comp (ab4 d)) := by
    rw [heq]
    apply zpH
    intro j
    change jB (t (tO (z9v j))) =
      s (jB (ab4 d (z9v j)))
    simp only [tO,ab4,zTw]
    rw [show t (KT PV j.val)= _ from dMp Q i a j,← htrim j]
    exact (hs (d j)).symm
  have hpoint (p:nW) :
      e (jR (zVv (oV Q) (tO p))) =
        s (jB (ab4 d p)) :=zmU hjet p
  have hinjR:zq4 jR:=zxb R _
  have hinjB:zq4 jB:=zxb B[X] _
  refine ⟨?_,?_⟩
  · ext p
    change tO p∈oV Q↔ab4 d p=0
    rw [← z1Q]
    constructor
    · intro hp
      apply s.injective.comp hinjB
      simp only [z3s,map_zero,← hpoint p,hp]
    · intro hp
      apply e.injective.comp hinjR
      simp only [z3s,map_zero,hpoint p,hp]
  · intro L _
    have hdim' : (zIU (oV Q)).natDegree=2 := by
      rw [oV,ZI,hdim]
    apply h2 (oV Q) B[X] (aWi L (oV Q)) (adv d L)
      (e.trans s.symm) hdim'
    intro p
    apply s.injective
    change s (s.symm (e (jR (zVv (oV Q) (tO
      (zIe L p))))))=s (jB (ab4 d (zIe L p)))
    rw [AlgEquiv.apply_symm_apply,hpoint]
end
end aFR
end
section
namespace bz0
noncomputable section
open cu gT DQ Cu UI XW
open aiN
open scoped Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:znc kM} {g n:ℕ}
 {R:wJ C₀ J g} (A:yI R n)
private abbrev S:=anh A
private abbrev E :=akF A
private abbrev T:=Jv (E A)
private abbrev Raw:=(a9Y A)[X]
local instance :CommSemiring (Raw A) :=
  @zEw (a9Y A)
    (@zEw (aao A)[X]
      (@zEw (aao A) (inferInstance :zrb (aao A)).toCommRing.toCommSemiring))
private abbrev quotientMap:z3y (Fin n) aQ →+* S A:=zVv _
private abbrev uZ:aQ →+* S A:=algebraMap aQ (S A)
private abbrev bv4 :DT n →+* S A :=
 (quotientMap A).comp (zDK (algebraMap L aQ))
private abbrev am5:Prop :=
 ∀ q:DT n,q∉TU A→ IsUnit (bv4 A q)
private def eJY:jo A →+* S A :=
 zP2 _ (bv4 A) fun _ h =>
  Ideal.Quotient.eq_zero_iff_mem.mpr (zKg (z7X _ h))
private def aTI (h:am5 A) :aao A →+* S A :=
 zvq (M:=nonZeroDivisors (jo A)) (g:=eJY A) fun d=> by
  obtain ⟨q,hq⟩:=zld (d:jo A)
  rw [← hq]
  apply h
  exact fun hq' => (mem_nonZeroDivisors_iff_ne_zero.mp d.prop)
   (hq ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hq')
private theorem bCV (h:am5 A) (q:DT n) :
  aTI A h (apG A q)=bv4 A q :=
 zX4 (M:=nonZeroDivisors (jo A)) _ _
private def bg2 :=uZ A (algebraMap FX aQ KK)
private def av8 (h:am5 A) :Raw A →+* S A :=
 zqf
  (zqf (zqf (aTI A h) (bg2 A))
    (uZ A (gT.ek 1))) (uZ A (gT.ek 0))
private def av9:Raw A →+* T A :=
 (algebraMap (E A)[X] (T A)).comp (zhd (amu A))
private abbrev UR:=z3y (Fin 2) L[X]
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance :zZE UR aQ :=
 ((algebraMap aZ aQ).comp (algebraMap UR aZ)).toAlgebra
local instance :SMul UR aQ:=(inferInstance :zZE UR aQ).toSMul
local instance :SMul aZ aQ:=(inferInstance :zZE aZ aQ).toSMul
local instance :zsf UR aZ aQ :=
 zsL (R:=UR) (S:=aZ) (A:=aQ) fun _=>rfl
private instance gRz :z0o UR aQ:= by
 let M:=(nonZeroDivisors L[X]).map (znf (σ:=Fin 2))
 let N :=nonZeroDivisors aZ
 have h:=IsLocalization.localization_localization_isLocalization_of_has_all_units
  M N aQ (fun _ h=>h.mem_nonZeroDivisors)
 have he :N.comap (algebraMap UR aZ)=nonZeroDivisors UR:= by
  ext s
  change (algebraMap UR aZ s)∈nonZeroDivisors aZ↔s∈nonZeroDivisors UR
  simp only [zu8,mem_nonZeroDivisors_iff_ne_zero,not_iff_not]
  exact (zNV _ (zxb L[X] FX)).eq_iff' (map_zero _)
 rw [he] at h
 exact h
@[simp] private theorem c64 (p:L[X]) :
    algebraMap UR aQ (znf p) =
      algebraMap FX aQ (algebraMap L[X] FX p) := by
  rw [zG3 UR aZ aQ,zu8,
    zpw]
  rfl
@[simp] private theorem c65 (i:Fin 2) :
   algebraMap UR aQ (z9v i)=gT.ek i:= by
  rw [zG3 UR aZ aQ,zu8,
   z7N]
  rfl
private def aka :aao A →+* Raw A :=
 Polynomial.C.comp (Polynomial.C.comp z1z)
private def bgx :L[X] →+* Raw A :=
 zqf (R:=L) (S:=Raw A)
  ((aka A).comp ((apG A).comp znf))
  (z1z (z1z (z7y: (aao A)[X])))
private def awo:UR →+* Raw A :=
 zOD (σ:=Fin 2) (R:=L[X]) (S₁:=Raw A) (bgx A)
  ![z7y,z1z z7y]
private theorem dcr (h:am5 A) :
    (av8 A h).comp (awo A) =
      (uZ A).comp (algebraMap UR aQ) := by
  apply zXT
  · have hc: (av8 A h).comp (bgx A) =
        (uZ A).comp ((algebraMap FX aQ).comp (algebraMap L[X] FX)) := by
      apply z86
      · intro c
        simp only [av8,bgx,aka,zQb,
          z4Q,zJU,bCV,zpw]
        change uZ A (algebraMap L aQ c) =
          uZ A (algebraMap FX aQ (algebraMap L[X] FX (algebraMap L L[X] c)))
        rw [← zG3 L L[X] FX,← zG3 L FX aQ]
      · simp [av8,bgx,bg2,KK]
    intro p
    simpa only [zQb,awo,zTv,c64]
      using zLs hc p
  · intro i
    fin_cases i <;> simp [awo,av8]
private theorem c2S {B:Type*} [za6 B] (v :z3y (Fin n) aQ →+* B)
    (p:XO n) :
    v (aIM p) =
      p.eval₂ (zqf (v.comp (zDK (algebraMap L aQ)))
        (v (znf (algebraMap FX aQ KK))))
        (v (znf (gT.ek 1))) := by
  rw [aIM,zly,ajx,zem]
  congr 1
  apply z86
  · intro q
    change v (zDK (algebraMap FX aQ)
      (zqf (zDK (algebraMap L FX)) (znf KK)
        (z1z q)))= _
    simp only [zQb,z4Q,zJU,
      z6Y,← zYY L FX aQ]
  · change v (zDK (algebraMap FX aQ)
      (zqf (zDK (algebraMap L FX)) (znf KK)
        z7y))= _
    simp
private theorem c5m {B:Type*} [za6 B]
   (v :aao A →+* B) (x y :B) :
   (aI7 A).eval₂ (zqf v x) y =
     A.equation.eval₂ (zqf (v.comp (apG A)) x) y := by
 rw [aI7,zem]
 congr 1
 apply z86 <;> simp
private theorem c63 (h:am5 A) (q:Raw A)
   (hq:av9 A q=0) :av8 A h q=0:= by
 let v :=zqf (aTI A h) (bg2 A)
 let y :=uZ A (gT.ek 1)
 have hp: (aI7 A).eval₂ v y=0:= by
   rw [c5m]
   have hc: (aTI A h).comp (apG A)=bv4 A :=
     zz4 (bCV A h)
   rw [hc]
   exact (c2S (quotientMap A) A.equation).symm.trans
     (Ideal.Quotient.eq_zero_iff_mem.mpr (zs0 (z5J _)))
 have hm:q.map (amu A)=0 :=
   zxb (E A)[X] (T A) (hq.trans (map_zero _).symm)
 have hz :q.map (zqf v y)=0:= by
   ext i
   rw [z0b,zO6]
   have hi:=congrArg (fun p: (E A)[X]=>p.coeff i) hm
   rw [z0b,zO6] at hi
   obtain ⟨r,hr⟩:=(c62 A _).mp hi
   simp only [hr,z4Q,zxy,hp,zero_mul]
 change q.eval₂ (zqf v y) _=0
 rw [Polynomial.eval₂_eq_eval_map,hz,Polynomial.eval_zero]
private def a8s (h:am5 A) (hne :Nontrivial (S A)) :aQ →+* T A :=
 zIj (g:=(av9 A).comp (awo A)) (by
  apply (zli _).mpr
  rw [zr7]
  intro p hp
  have hz :=c63 A h (awo A p) hp
  rw [← zQb,dcr] at hz
  exact ((uZ A).injective.comp (zxb UR aQ))
   (hz.trans (map_zero ((uZ A).comp (algebraMap UR aQ))).symm))
private theorem bNG (h:am5 A) (hne :Nontrivial (S A)) (p:UR) :
  a8s A h hne (algebraMap UR aQ p)=av9 A (awo A p) :=
 zoc (g:=(av9 A).comp (awo A)) _ _
private theorem a8t (h:am5 A) (hne :Nontrivial (S A)) :
    aYW (aq1 A) (bcB A) (a8s A h hne) := by
  refine ⟨?_,?_,?_⟩
  · have hb: (a8s A h hne).comp (algebraMap FX aQ) =
        (IN (E A)).comp (aq1 A) := by
      apply z2O (A:=L[X])
      have hc: ((a8s A h hne).comp (algebraMap UR aQ)).comp znf =
          ((IN (E A)).comp (aq1 A)).comp (algebraMap L[X] FX) := by
        apply z86
        · intro c
          rw [zQb,zQb,bNG]
          simp only [awo,bgx,aka,av9,zQb,
            zTv,z4Q,zJU,
            zKC,zrL,amu,bXF,
            arT]
          change IN (E A) (aq1 A (algebraMap L FX c)) =
            IN (E A) (aq1 A (algebraMap L[X] FX (algebraMap L L[X] c)))
          rw [← zG3 L L[X] FX]
        · rw [zQb,zQb,bNG]
          simp [awo,bgx,av9,amu,IN,KK]
      intro p
      simpa only [zQb,c64] using zLs hc p
    exact zLs hb
  · rw [← c65 1,bNG]
    simp [awo,av9,amu,IN]
  · rw [← c65 0,bNG]
    simp [awo,av9,awC]
private def aUn (h:am5 A) (hne :Nontrivial (S A)) :
  z3y (Fin n) aQ →+* T A :=
 zOD (a8s A h hne) (IN (E A) ∘ bXX A)
private theorem b1Q (h:am5 A) (hne :Nontrivial (S A)) :
   (aUn A h hne).comp (zDK (algebraMap L aQ)) =
     (IN (E A)).comp (arT A) := by
 apply zXT
 · intro c
   simp only [zQb,zpw,aUn,zTv,arT]
   rw [zG3 L FX aQ,(a8t A h hne).1]
 · intro i
   simp [aUn,arT]
private def aP7 (h:am5 A) (hne :Nontrivial (S A)) :S A →+* T A :=
  zP2 _ (aUn A h hne) (by
    apply (show _≤zdq (aUn A h hne) from ?_)
    apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro p hp
      change ((aUn A h hne).comp (zDK (algebraMap L aQ))) p=0
      rw [b1Q,zQb,
        RingHom.mem_ker.mp (show p∈zdq (arT A) from (cbl A).symm ▸ hp),
        map_zero]
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟩
      change aUn A h hne (aIM A.equation)=0
      rw [c2S,b1Q]
      simp only [aUn,zTv,
        (a8t A h hne).1,(a8t A h hne).2.1]
      have hv : (IN (E A)).comp (arT A) =
          ((IN (E A)).comp (aCG A)).comp (apG A) :=
        zz4 fun p=> by simp
      rw [hv,← c5m]
      have hr :amu A (aI7 A)=0:=(c62 A _).mpr dvd_rfl
      have hx :zqf ((IN (E A)).comp (aCG A))
          (IN (E A) (aq1 A KK)) =
          (IN (E A)).comp (zqf (aCG A) (aq1 A KK)) := by
        apply z86 <;> simp
      rw [hx,← zly]
      exact (IN (E A)).map_zero' ▸ congrArg (IN (E A)) hr)
private theorem bNt (h:am5 A) (hne :Nontrivial (S A)) :
  (aP7 A h hne).comp (uZ A)=a8s A h hne := by
 ext p
 exact zTv _ _ _
private theorem dct (h:am5 A) (hne :Nontrivial (S A)) :
    (aP7 A h hne).comp (av8 A h)=av9 A:= by
  let e :=aP7 A h hne
  let b:=a8s A h hne
  have hs : ∀ p,e (uZ A p)=b p:=zLs (bNt A h hne)
  have ho:=a8t A h hne
  have hc:e.comp (aTI A h)=(IN (E A)).comp (aCG A) := by
    apply z2O (A:=jo A)
    intro a
    obtain ⟨q,rfl⟩:=zld a
    change e (aTI A h (apG A q)) =
      IN (E A) (aCG A (apG A q))
    rw [bCV,bXF]
    exact zLs (b1Q A h hne) q
  have hx :e.comp (zqf (aTI A h) (bg2 A)) =
      (IN (E A)).comp (zqf (aCG A) (aq1 A KK)) := by
    apply z86
    · simpa only [zQb,z4Q,zJU] using
        zLs hc
    · simpa only [zQb,z4Q,zC9,bg2,hs]
        using ho.1 KK
  have hy :e.comp (zqf
      (zqf (aTI A h) (bg2 A))
      (uZ A (gT.ek 1)))=(IN (E A)).comp (amu A) := by
    apply z86
    · simpa only [zQb,amu,z4Q,zJU] using
        zLs hx
    · simp only [zQb,amu,z4Q,zC9]
      rw [hs]
      exact ho.2.1
  apply z86
  · simpa only [zQb,av8,av9,z4Q,
      zJU,zKC,zrL,IN] using
      zLs hy
  · simp only [zQb,av8,av9,z4Q,
      zC9,zKC,zSo]
    change e (uZ A (gT.ek 0))=awC (E A)
    rw [hs]
    exact ho.2.2
private theorem dcs (h:am5 A) (hne :Nontrivial (S A)) :
    zq4 (aP7 A h hne) := by
  rw [zli,zr7]
  intro s hs
  obtain ⟨f,rfl⟩:=zld s
  let M:=(nonZeroDivisors UR).map (znf (σ:=Fin n))
  obtain ⟨⟨q,d⟩,hd⟩:=IsLocalization.surj M f
  obtain ⟨a,ha,had⟩:=d.prop
  have he : (quotientMap A).comp (algebraMap (z3y (Fin n) UR) (z3y (Fin n) aQ)) =
      (av8 A h).comp (zOD (awo A)
        (z1z ∘ z1z ∘ z1z ∘ apG A ∘ z9v)) := by
    apply zXT
    · intro p
      simp only [zQb,zu8,zpw,
        zTv]
      exact (zLs (dcr A h) p).symm
    · intro i
      simp only [zQb,zu8,z7N,
        zrD,z3s,av8,z4Q,
        zJU,bCV,bv4]
  let r :Raw A:=zOD (awo A)
    (z1z ∘ z1z ∘ z1z ∘ apG A ∘ z9v) q
  have hmul :quotientMap A f*uZ A (algebraMap UR aQ a)=av8 A h r := by
    let m:=algebraMap (z3y (Fin n) UR) (z3y (Fin n) aQ)
    calc
      _=quotientMap A (f*m d) := by
        rw [map_mul,← had,show m=zDK (algebraMap UR aQ) from rfl,
          zpw]
        rfl
      _=((quotientMap A).comp m) q:=congrArg (quotientMap A) hd
      _ = _:=zLs he q
  have hzero :av9 A r=0:= by
    rw [← zLs (dct A h hne) r,zQb,← hmul,map_mul]
    rw [show aP7 A h hne (quotientMap A f)=0 from hs,zero_mul]
  rw [c63 A h r hzero] at hmul
  exact ((z0j aQ ⟨a,ha⟩).map (uZ A)).mul_left_eq_zero.mp hmul
private theorem gnC (h:am5 A) (hne :Nontrivial (S A))
    (hf :zAa aQ (S A)) :zpX (aP7 A h hne) := by
  let e :=aP7 A h hne
  let:ztn (S A) :=(dcs A h hne).isDomain e
  let:zrb (S A) :=(IsField.of_isDomain_of_finite aQ (S A)).toField
  let U:=e.fieldRange
  let:zZE FX (EC R) :=(amB R).toAlgebra
  let V:IntermediateField FX (EC R) :=
    { (U.comap (IN (E A))).map (auC A) with
      algebraMap_mem' := fun x=>⟨aq1 A x,
        ⟨uZ A (algebraMap FX aQ x),by
          rw [← (a8t A h hne).1 x]
          exact zLs (bNt A h hne) _⟩,rfl⟩ }
  have hraw (q:a9Y A) :IN (E A) (amu A q)∈U :=
    ⟨av8 A h (z1z q),by
      simpa only [zQb,av9,zKC,zrL,IN]
        using zLs (dct A h hne) (z1z q)⟩
  have hV:bcC A≤V:= by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ (⟨i,rfl⟩ | hi)
    · refine ⟨bXX A i,?_,rfl⟩
      simpa [amu,arT] using
        hraw (z1z (z1z (apG A (z9v i))))
    · obtain rfl :=Set.mem_singleton_iff.mp hi
      refine ⟨bcB A,?_,rfl⟩
      simpa [amu] using hraw z7y
  have hconst (a :E A) :IN (E A) a∈U:= by
    obtain ⟨v,hv,heq⟩:=hV a.property
    exact (auC A).injective heq ▸ hv
  have ht:awC (E A)∈U :=
    ⟨uZ A (gT.ek 0),(zLs (bNt A h hne) _).trans
      (a8t A h hne).2.2⟩
  intro z
  change z∈U
  have hpoly :zxp (algebraMap (E A)[X] (T A))⊆U:= by
    rintro _ ⟨p,rfl⟩
    let v :=zqf ((IN (E A)).codRestrict U.toSubring hconst)
      (⟨awC (E A),ht⟩:U.toSubring)
    have hv :U.toSubring.subtype.comp v=algebraMap (E A)[X] (T A) := by
      apply z86
      · intro a
        simp only [v,zQb,z4Q,zJU]
        rfl
      · simp only [v,zQb,z4Q,zC9]
        rfl
    exact (zLs hv p) ▸ (v p).property
  have hall: (⊤ : Subfield (T A))≤U:= by
    rw [← IsFractionRing.closure_range_algebraMap (E A)[X] (T A)]
    exact Subfield.closure_le.mpr hpoly
  exact hall (Subfield.mem_top _)
theorem proof :aiN.c1 := by
 intro C₀ _ J g n R A _ hfin hne hd
 let e :=aP7 A hd hne
 refine ⟨RingEquiv.ofBijective e
  ⟨dcs A hd hne,gnC A hd hne hfin⟩,?_⟩
 change aYW (aq1 A) (bcB A)
  ((aP7 A hd hne).comp (uZ A))
 exact (bNt A hd hne).symm ▸ a8t A hd hne
end
end bz0
end
section
namespace axc
noncomputable section
open MvPolynomial
variable {k σ:Type*} [zrb k]
def VW (I:znc (z3y σ k)) (f :z3y σ k) :
    znc (z3y σ k) :=
  I.colon (zye {f})
def ahw (I:znc (z3y σ k)) (f :z3y σ k) :
    znc (z3y σ k) :=
  I ⊔ zye {f}
theorem arO {I:znc (z3y σ k)} {f a :z3y σ k} :
  a∈VW I f↔a*f∈I :=
 Ideal.mem_colon_span_singleton
theorem euZ (I:znc (z3y σ k)) (f :z3y σ k) :
  I≤VW I f :=
 fun _ ha ↦ arO.mpr (I.mul_mem_right f ha)
theorem bIl (I:znc (z3y σ k)) (f :z3y σ k) :
 I≤ahw I f :=le_sup_left
end
end axc
end
section
namespace axc
open MvPolynomial
open Ey
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type*} [zrb k]
theorem eog (I:znc (z3y σ k)) :
  (adN I).IsHomogeneous (homogeneousSubmodule σ k) := by
 apply zqZ
 rintro _ ⟨f,_,rfl⟩
 exact ⟨f.totalDegree,homogeneousComponent_mem _ _⟩
theorem dTk {I:znc (z3y σ k)} {f :z3y σ k} {d:ℕ}
  (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) (hf :f.IsHomogeneous d) :
  (ahw I f).IsHomogeneous (homogeneousSubmodule σ k) := by
 apply hI.sup
 apply zqZ
 intro g hg
 rw [Set.mem_singleton_iff.mp hg]
 exact ⟨d,hf⟩
theorem dTl {I:znc (z3y σ k)} {f :z3y σ k}
  (hf :f∉I) :I<ahw I f := by
 refine lt_of_le_not_ge (bIl I f) (fun h ↦ hf (h ?_))
 exact zs0 (z5J f)
theorem cJf {I:znc (z3y σ k)}
  {f :z3y σ k} {d:ℕ}
  (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) (hf :f.IsHomogeneous d) :
  (VW I f).IsHomogeneous (homogeneousSubmodule σ k) := by
 intro i a ha
 rw [arO] at ha ⊢
 have hm:=hI (i+d) ha
 rwa [DirectSum.coe_decompose_mul_add_of_right_mem (homogeneousSubmodule σ k) hf] at hm
theorem d4k [Finite σ] {I:znc (z3y σ k)}
    (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) (hproper :I ≠ ⊤) :
    ∃ (d:ℕ) (f :z3y σ k),
      f.IsHomogeneous d∧f∉I∧(VW I f).IsPrime := by
  classical
  let candidates :Set (znc (z3y σ k)) :=
    {Q | ∃ (d:ℕ) (f :z3y σ k),
      f.IsHomogeneous d∧f∉I∧Q=VW I f}
  have hone : (1 :z3y σ k)∉I :=
    fun h ↦ hproper (zAn I h isUnit_one)
  obtain ⟨_,⟨d,f,hf,hfI,rfl⟩,hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr
      (inferInstance :IsNoetherianRing (z3y σ k)) candidates
      ⟨VW I 1,0,1,isHomogeneous_one _ _,hone,rfl⟩
  refine ⟨d,f,hf,hfI,(cJf hI hf).isPrime_of_homogeneous_mem_or_mem
    ?_ ?_⟩
  · intro htop
    apply hfI
    simpa using arO.mp
      (show (1 :z3y σ k)∈VW I f by rw [htop]; trivial)
  · intro a b ha _ hab
    by_cases haI:a∈VW I f
    · exact Or.inl haI
    · apply Or.inr
      have hle :VW I f≤VW I (a*f) := by
        intro c hc
        apply arO.mpr
        rw [mul_left_comm]
        exact I.mul_mem_left a (arO.mp hc)
      obtain ⟨e,he⟩:=ha
      have hmem:VW I (a*f)∈candidates :=
        ⟨e+d,a*f,he.mul hf,mt arO.mpr haI,rfl⟩
      rw [hle.eq_of_not_lt (hmax _ hmem)]
      exact arO.mpr (by rw [← mul_assoc,mul_comm b a]; exact arO.mp hab)
end axc
end
section
namespace bzZ
noncomputable section
open MvPolynomial NS XW
set_option maxHeartbeats 1000000
private theorem dzZ {k σ:Type*} [zrb k] [Finite σ]
    {I:znc (z3y σ k)} {f :z3y σ k} (hf :f.totalDegree≤1)
    (hd: (affineHilbertPolynomial I).natDegree≤1)
    (h:ahc I (homogeneousComponent 1 f)) :
    ∃ N :ℕ,∀ d:ℕ,N≤d → ∀ x∈quotientDegreeLE I (d+1),
      zVv I f*x∈quotientDegreeLE I (d+1)→x∈quotientDegreeLE I d:= by
  have hc:f - homogeneousComponent 1 f=znf (f.coeff 0) := by
    classical
    ext m
    rw [coeff_sub,coeff_homogeneousComponent,coeff_C]
    by_cases hm:m=0
    · subst m
      simp
    by_cases hn:m.degree=1
    · simp [hn,Ne.symm hm]
    have hz :f.coeff m=0:=coeff_eq_zero_of_totalDegree_lt
      (show f.totalDegree< m.degree from by
        have h0:m.degree≠0:= fun he=>hm ((Finsupp.degree_eq_zero_iff m).mp he)
        omega)
    simp [hn,Ne.symm hm,hz]
  obtain ⟨N,hN⟩:=h
  obtain ⟨M,hM⟩:=exists_eval_affineHilbertPolynomial I
  refine ⟨max N M,fun d hdm x hx hfx => ?_⟩
  let U:=quotientDegreeLE I d
  let V:=quotientDegreeLE I (d+1)
  let W:=quotientDegreeLE I (d+2)
  let U' := U.comap V.subtype
  let V' := V.comap W.subtype
  have hUV:U≤V:=quotientDegreeLE_mono I (by omega)
  have hVW:V≤W:=quotientDegreeLE_mono I (by omega)
  let μ:V →ₗ[k] W:=((zzN k (zVv I f)).domRestrict V).codRestrict W
    (fun z=> by
      change zVv I f*z.val∈quotientDegreeLE I (d+2)
      simpa only [zg2 1,Nat.add_assoc] using
        (mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE (I:=I) hf) z.property))
  let φ:=V'.mkQ.comp μ
  have hφ:zpX φ:= by
    intro q
    obtain ⟨z,rfl⟩:=V'.mkQ_surjective q
    obtain ⟨a,ha,b,hb,he⟩:=hN (d+1) (by omega) z.val z.property
    refine ⟨⟨b,hb⟩,?_⟩
    change V'.mkQ (μ ⟨b,hb⟩)=V'.mkQ z
    apply (Submodule.Quotient.eq V').mpr
    change zVv I f*b - z.val∈V
    rw [he,sub_add_eq_sub_sub,sub_right_comm,← sub_mul,← map_sub,hc]
    have hC:zVv I (znf (f.coeff 0))∈quotientDegreeLE I 0 :=
      mk_mem_quotientDegreeLE (totalDegree_C _).le
    exact V.sub_mem (by simpa only [zero_add] using mul_mem_quotientDegreeLE hC hb) ha
  have hk :U' ≤ z83 φ:= by
    intro z hz
    rw [LinearMap.mem_ker]
    exact (ziM _).mpr (by
      change zVv I f*z.val∈quotientDegreeLE I (d+1)
      simpa only [zg2 1] using
        (mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE (I:=I) hf) (show z.val∈U from hz)))
  have hnull:=φ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hφ,finrank_top] at hnull
  have hquot:=V'.finrank_quotient_add_finrank
  rw [(zTz hVW).finrank_eq] at hquot
  have hlinear :zsE k W+Module.finrank k U=2*zsE k V:= by
    change affineHilbertFunction I (d+2)+affineHilbertFunction I d =
      2*affineHilbertFunction I (d+1)
    have hP (z :ℚ) : (affineHilbertPolynomial I).eval z =
        (affineHilbertPolynomial I).coeff 1*z+(affineHilbertPolynomial I).coeff 0:= by
      nth_rw 1 [Polynomial.eq_X_add_C_of_natDegree_le_one hd]
      simp
    have h (i:ℕ) : (affineHilbertFunction I (d+i) :ℚ) =
        (affineHilbertPolynomial I).coeff 1*((d:ℚ)+i) +
        (affineHilbertPolynomial I).coeff 0:= by
      rw [← hM (d+i) (by omega),hP,z6H]
    have hr :=h 0
    simp only [Nat.cast_zero,add_zero] at hr
    exact_mod_cast (show (affineHilbertFunction I (d+2) :ℚ)+affineHilbertFunction I d =
      2*affineHilbertFunction I (d+1) by rw [h 2,hr,h 1]; push_cast; ring)
  have heq :U' = z83 φ:=Submodule.eq_of_le_of_finrank_eq hk (by
    rw [(zTz hUV).finrank_eq]
    omega)
  have hx' : (⟨x,hx⟩:V)∈z83 φ:=LinearMap.mem_ker.mpr
    ((ziM _).mpr hfx)
  rw [← heq] at hx'
  exact hx'
section Geometry
variable {k E F σ ι:Type*} [zrb k] [zrb E] [zrb F]
private theorem bIT (a :k →+* E) (p:z3y σ k) (d:ℕ) :
  map a (homogeneousComponent d p)=homogeneousComponent d (map a p) := by
 ext m
 by_cases hm:m.degree=d <;>
  simp only [coeff_map,coeff_homogeneousComponent,hm,ite_true,ite_false,map_zero]
private theorem bO9 (a :k →+* E) (p:z3y σ k) :
  (map a p).totalDegree≤p.totalDegree :=
 zRS (support_map_subset a p)
variable [zZE k E] [zZE E F] [zZE k F] [zsf k E F]
private theorem dzX (I:znc (z3y σ k)) :
  (lW I).map (map (algebraMap k E))≤lW (Gu E I) := by
 apply Ideal.map_le_iff_le_comap.mpr
 apply Ideal.span_le.mpr
 rintro _ ⟨p,d,hp,hd,rfl⟩
 change map _ (homogeneousComponent d p)∈lW _
 rw [bIT]
 exact zCn ⟨map _ p,d,z7X _ hp,
  (bO9 _ _).trans hd,rfl⟩
private theorem aUp (p:z3y σ k) (b:σ→F) :
  aeval b (map (algebraMap k E) p)=(aeval b p:F) := by
 rw [aeval_def,eval₂_map,← zYY,← aeval_def]
private theorem aNz [z85 σ] {p:z3y σ k} {d:ℕ}
   (hp:p.IsHomogeneous d) (x :σ→F) (t:F) :
   (aeval (fun i=>t*x i) p:F)=t^d*aeval x p:= by
 classical
 simp only [aeval_def,eval₂_eq',zxw]
 refine zUo rfl fun m hm => ?_
 have he :m.degree=d:= by
   by_contra h
   exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
 rw [show (∏ i:σ,(t*x i)^m i)=t^d * ∏ i:σ,x i^m i by
   simp only [mul_pow,zeY,zX0,
     ← zFi,he]]
 ac_rfl
private theorem normalize [z85 σ] [LinearOrder σ] [WellFoundedGT σ] [IsAlgClosed k]
   (I:znc (z3y σ k)) (hd: (affineHilbertPolynomial I).natDegree=1)
   {x :σ→F} (hx :x∈zeroLocus F (lW (Gu E I)))
   {i:σ} (hi:x i≠0) :
   ∃ b:σ→k,b∈zeroLocus k (lW I)∧b i=1 ∧
     (algebraMap k F ∘ b)=fun j=>(x i)⁻¹*x j:= by
 let y :σ→F:= fun j=>(x i)⁻¹*x j
 have hy :y i=1 :=inv_mul_cancel₀ hi
 have hx' : x∈zeroLocus F (lW I) := by
   intro p hp
   rw [← aUp (E :=E)]
   exact hx _ (dzX I (z7X _ hp))
 have hyB:lW I≤zdq (aeval y).toRingHom:= by
   apply Ideal.span_le.mpr
   rintro _ ⟨p,d,hp,hn,rfl⟩
   change (aeval y (homogeneousComponent d p) :F)=0
   rw [aNz (homogeneousComponent_isHomogeneous ..),hx' _ (zCn
     ⟨p,d,hp,hn,rfl⟩),mul_zero]
 have hyC:y∈zeroLocus F (KL I i) := by
   change KL I i≤zdq (aeval y).toRingHom
   refine sup_le hyB (Ideal.span_le.mpr ?_)
   rintro _ (rfl :_=z9v i - 1)
   change (aeval y (z9v i - 1 :z3y σ k) :F)=0
   simp [hy]
 let J:=KL I i
 let:zAa k (z3y σ k ⧸ J) :=
   moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero
     (YT.bmo I hd i)
 let e : (z3y σ k ⧸ J) →ₐ[k] F:=zTA J (aeval y) hyC
 have hroot (j:σ) :IsIntegral k (y j) := by
   have h:=(zmn (R:=k)
     (zVv J (z9v j))).map e
   change IsIntegral k ((aeval y) (z9v j:z3y σ k)) at h
   simpa only [aeval_X] using h
 have hconstant (j:σ) : ∃ b:k,algebraMap k F b=y j:= by
   apply (hroot j).mem_range_algHom_of_minpoly_splits (K:=k) _ (zNX k F)
   simpa only [zCp,zei] using IsAlgClosed.splits (minpoly k (y j))
 choose b hb using hconstant
 have hb' : algebraMap k F ∘ b=y :=funext hb
 refine ⟨b,?_,(algebraMap k F).injective ((hb i).trans (hy.trans (map_one _).symm)),hb'⟩
 intro p hp
 apply (algebraMap k F).injective
 rw [map_zero]
 change (zNX k F) (aeval b p)=0
 rw [zrc,show (fun i=>(zNX k F) (b i))=y from hb']
 exact hyB hp
private theorem eMt [z85 σ] [IsAlgClosed k]
  (I:znc (z3y σ k)) (hI:I.IsPrime) :
  ∃ b:σ→k,b∈zeroLocus k I:= by
 by_contra! h
 have hZ:zeroLocus k I = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
 let:I.IsPrime :=hI
 have he :=MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K:=k) I
 rw [hZ] at he
 apply hI.ne_top
 rw [← he]
 exact top_unique fun p _ b hb=>False.elim hb
private theorem cMP [z85 ι] (p:ι→z3y σ k) (w:ι→E)
   (hw:z14 k w) (b:σ→k)
   (h: (eval (algebraMap k E ∘ b))
     (∑ s,znf (w s)*map (algebraMap k E) (p s))=0) :
   ∀ s,eval b (p s)=0:= by
 apply (Fintype.linearIndependent_iff.mp hw) (fun s=>eval b (p s))
 rw [map_sum] at h
 simpa only [map_mul,eval_C,eval_map,← z6r,
   zd5,mul_comm] using h
theorem c7W [z85 σ] [LinearOrder σ] [WellFoundedGT σ] [z85 ι]
    [IsAlgClosed k] (I:znc (z3y σ k)) (hI:I.IsPrime)
    (p:ι→z3y σ k) (w:ι→E) (hw:z14 k w)
    (hp : ∀ s,(p s).totalDegree≤1)
    (haff : ∀ b∈zeroLocus k I,∃ s,eval b (p s)≠0)
    (hinf : ∀ b∈zeroLocus k (lW I),
      (∀ s,eval b (homogeneousComponent 1 (p s))=0)→b=0)
    (hd: (affineHilbertPolynomial I).natDegree≤1) :
    atV (Gu E I)
      (∑ s,znf (w s)*map (algebraMap k E) (p s)) := by
  let J:=Gu E I
  let f :z3y σ E := ∑ s,znf (w s)*map (algebraMap k E) (p s)
  have hf :f.totalDegree≤1 := by
    apply totalDegree_finsetSum_le
    intro s _
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C,zero_add]
    exact (bO9 _ _).trans (hp s)
  have hJ:J.IsPrime :=aA7.beK I hI
  have hne :zVv J f≠0:= by
    obtain ⟨b,hb⟩:=eMt I hI
    obtain ⟨s,hs⟩:=haff b hb
    have hb' : (algebraMap k E ∘ b)∈zeroLocus E J:= by
      change J≤zdq (aeval (algebraMap k E ∘ b)).toRingHom
      apply Ideal.map_le_iff_le_comap.mpr
      intro q hq
      change (aeval _ (map (algebraMap k E) q) :E)=0
      rw [aUp]
      change (aeval (fun i=>(zNX k E) (b i)) q:E)=0
      rw [← zrc b (zNX k E),hb q hq,map_zero]
    intro hz
    apply hs
    exact cMP p w hw b (by
      rw [← aeval_eq_eval]
      exact hb' f (Ideal.Quotient.eq_zero_iff_mem.mp hz)) s
  refine ⟨hf,(IsRegular.of_ne_zero hne).1,?_⟩
  have hdJ:affineHilbertPolynomial J=affineHilbertPolynomial I :=
    Ey.ZI I
  by_cases hz : (affineHilbertPolynomial I).natDegree=0
  · let:zAa E (z3y σ E ⧸ J) :=
      moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero (hdJ.symm ▸ hz)
    obtain ⟨N,hN⟩:=exists_quotientDegreeLE_eq_top J
    exact ⟨N,fun d hd x _ _=> by rw [hN d hd]; trivial⟩
  have hdim: (affineHilbertPolynomial I).natDegree=1 := by omega
  let l:=homogeneousComponent 1 f
  have hreduce :ahc J l:= by
    apply YT.bPG (K:=AlgebraicClosure E) _
      (homogeneousComponent_isHomogeneous ..)
    intro x hx hval
    funext i
    change x i=0
    by_contra hi
    obtain ⟨b,hb,hbi,he⟩:=normalize I hdim hx hi
    have hcut: (aeval (algebraMap k (AlgebraicClosure E) ∘ b) l:AlgebraicClosure E)=0:= by
      rw [he,aNz (homogeneousComponent_isHomogeneous ..),hval,mul_zero]
    have heval :eval (algebraMap k E ∘ b) l=0:= by
      apply (algebraMap E (AlgebraicClosure E)).injective
      rw [map_zero,← aeval_eq_eval]
      change (zNX E (AlgebraicClosure E)) (aeval _ l)=0
      rw [zrc]
      change (aeval (fun i=>algebraMap E (AlgebraicClosure E) (algebraMap k E (b i))) l :
        AlgebraicClosure E)=0
      simp_rw [← zG3 k E (AlgebraicClosure E)]
      exact hcut
    have hl:l = ∑ s,znf (w s) *
        map (algebraMap k E) (homogeneousComponent 1 (p s)) := by
      simp only [l,f,map_sum,homogeneousComponent_C_mul,bIT]
    rw [hl] at heval
    have hb0:=hinf b hb (cMP _ w hw b heval)
    rw [hb0] at hbi
    exact zero_ne_one hbi
  exact dzZ hf (hdJ ▸ hd) hreduce
end Geometry
end
end bzZ
end
section
namespace axc
open MvPolynomial Ey NS
variable {k σ:Type*} [zrb k]
theorem eoe (I:znc (z3y σ k)) :
   adN I=lW I:= by
 apply le_antisymm
 · apply Ideal.span_le.mpr
   rintro _ ⟨f,hf,rfl⟩
   exact zCn ⟨f,f.totalDegree,hf,le_rfl,rfl⟩
 · apply Ideal.span_le.mpr
   rintro _ ⟨f,n,hf,hn,rfl⟩
   rcases eq_or_lt_of_le hn with h | h
   · subst n
     exact zCn ⟨f,hf,rfl⟩
   · rw [homogeneousComponent_eq_zero _ _ h]
     exact znl _
theorem em4 [LinearOrder σ] [WellFoundedGT σ] [Finite σ]
   (I:znc (z3y σ k)) :
   affineHilbertPolynomial (adN I)=affineHilbertPolynomial I :=
 (congrArg affineHilbertPolynomial (eoe I)).trans
   (YT.bqR I)
end axc
end
section
namespace axc
noncomputable section
open aR B7 Ey MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 :Prop :=
  ∀ (I:znc jo) (f :jo) (d:ℕ),
    I.IsHomogeneous (homogeneousSubmodule rS ao) →
    f.IsHomogeneous d→f∉I→(VW I f).IsPrime →
    affineHilbertPolynomial I =
      affineHilbertPolynomial (ahw I f) +
        Polynomial.taylor (-(d:ℚ)) (affineHilbertPolynomial (VW I f))
def c2 :Prop :=
  ∀ (I:znc jo) (f :jo) (L:Fin 2→nW),
    zAa MY (ay5 L (oV I)) →
    zAa MY (ay5 L (oV (ahw I f))) ∧
      adI L (oV I) =
        adI L (oV (ahw I f)) +
        adI L (oV (VW I f))
private theorem cAV {I:znc jo}
  (h: (affineHilbertPolynomial I).natDegree=2) :
  affineDegree I=2*(affineHilbertPolynomial I).coeff 2 := by
 norm_num [affineDegree,z4w,h]
private theorem dNx (hHilbert:c1) (hFiber :c2) (I:znc jo) :
    I.IsHomogeneous (homogeneousSubmodule rS ao) →
    (affineHilbertPolynomial I).natDegree≤2 →
    ∃ (n:ℕ) (Q:Fin n→ znc jo),
      (∀ i,I≤Q i∧(Q i).IsPrime ∧
        (Q i).IsHomogeneous (homogeneousSubmodule rS ao) ∧
        (affineHilbertPolynomial (Q i)).natDegree=2) ∧
      (2 :ℚ)*(affineHilbertPolynomial I).coeff 2 = ∑ i,affineDegree (Q i) ∧
      ∀ (L:Fin 2→nW),zAa MY (ay5 L (oV I)) →
        (∑ i,adI L (oV (Q i))) ≤
          adI L (oV I) := by
  classical
  have :WellFoundedGT (znc jo) :=
    isNoetherian_iff.mp (inferInstance :IsNoetherianRing jo)
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    intro hI hdim
    by_cases htop:I = ⊤
    · subst I
      exact ⟨0,Fin.elim0,fun i ↦ i.elim0,by simp,fun L _ ↦ by simp⟩
    obtain ⟨d,f,hf,hfI,hprime⟩:=d4k hI htop
    let J:=ahw I f
    let R:=VW I f
    have hIJ:I≤J:=bIl I f
    have hIR:I≤R:=euZ I f
    have hdimJ:=(natDegree_affineHilbertPolynomial_le_of_le hIJ).trans hdim
    have hdimR:=(natDegree_affineHilbertPolynomial_le_of_le hIR).trans hdim
    obtain ⟨n,Q,hQ,hcoeffJ,hboundJ⟩ :=
      ih J (dTl hfI) (dTk hI hf) hdimJ
    have hcoeff : (affineHilbertPolynomial I).coeff 2 =
        (affineHilbertPolynomial J).coeff 2+(affineHilbertPolynomial R).coeff 2 := by
      rw [hHilbert I f d hI hf hfI hprime,Polynomial.coeff_add,Polynomial.coeff_taylor_of_natDegree_le _ hdimR]
    by_cases he : (affineHilbertPolynomial R).natDegree=2
    · refine ⟨n+1,z4W R Q,?_,?_,?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa only [zhe] using And.intro hIR
            (And.intro hprime (And.intro (cJf hI hf) he))
        · obtain ⟨hJQ,hq,hhom,hdegree⟩:=hQ j
          simpa only [zVG] using And.intro (hIJ.trans hJQ)
            (And.intro hq (And.intro hhom hdegree))
      · simp only [zCS,zhe,zVG]
        rw [hcoeff,mul_add,hcoeffJ,cAV he]
        exact add_comm _ _
      · intro L hfinite
        obtain ⟨hfiniteJ,hdimEq⟩:=hFiber I f L hfinite
        rw [zCS,zhe,hdimEq,add_comm
          (adI L (oV J))]
        simp only [zVG]
        exact Nat.add_le_add_left (hboundJ L hfiniteJ) _
    · refine ⟨n,Q,fun i ↦ ⟨hIJ.trans (hQ i).1,(hQ i).2⟩,?_,?_⟩
      · rw [hcoeff,zQl (lt_of_le_of_ne hdimR he),add_zero]
        exact hcoeffJ
      · intro L hfinite
        obtain ⟨hfiniteJ,hdimEq⟩:=hFiber I f L hfinite
        rw [hdimEq]
        exact (hboundJ L hfiniteJ).trans (Nat.le_add_right _ _)
private theorem eAq (I Q:znc jo) (hIQ:I≤Q)
  (hQ:Q.IsPrime) (hdim: (affineHilbertPolynomial I).natDegree≤2)
  (hQdim: (affineHilbertPolynomial Q).natDegree=2) :
  Q∈I.minimalPrimes := by
 refine ⟨⟨hQ,hIQ⟩,?_⟩
 intro R hR hRQ
 by_contra hQR
 obtain ⟨f,hfQ,hfR⟩:=Set.not_subset.mp
  (show ¬ (Q:Set jo)⊆(R:Set jo) from hQR)
 have hcut:R ⊔ zye {f} ≤ Q:=sup_le hRQ (Q.span_singleton_le_iff_mem.mpr hfQ)
 have hQle :=natDegree_affineHilbertPolynomial_le_of_le hcut
 have hdrop :=
  (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hR.1 hfR (b:=f.totalDegree) le_rfl).1
 have hRdim:=(natDegree_affineHilbertPolynomial_le_of_le hR.2).trans hdim
 omega
theorem of_children (h1 :c1) (h2 :c2) :Ey.c2 := by
 intro P _ hdim
 have hpoly :=em4 P
 have hinf : (affineHilbertPolynomial (adN P)).natDegree=2 := by
   rw [hpoly,hdim]
 obtain ⟨n,Q,hQ,hcoeff,hfiber⟩ :=
   dNx h1 h2 (adN P) (eog P) hinf.le
 refine ⟨n,Q,?_,?_,hfiber⟩
 · intro i
   obtain ⟨hle,hprime,hhom,hd⟩:=hQ i
   exact ⟨eAq _ _ hle hprime hinf.le hd,hhom,hd⟩
 · rw [hpoly] at hcoeff
   exact (cAV hdim).trans hcoeff
end
end axc
end
section
namespace cx3
noncomputable section
open MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1500000
private theorem aNz {k T σ:Type} [zrb k] [za6 T] [zZE k T]
  (v :σ→T) (u:T) {p:z3y σ k} {n:ℕ} (hp:p.IsHomogeneous n) :
  aeval (fun j=>u*v j) p=u^n*aeval v p:= by
 classical
 have he :=(homogeneousComponent_eq_self hp).symm.trans (homogeneousComponent_apply n p)
 simp only [aeval_eq_eval₂Hom]
 rw [he,map_sum,map_sum,zxw]
 apply zUo rfl
 intro d hd
 have hdeg:d.degree=n:=(Finset.mem_filter.mp hd).2
 simp only [eval₂Hom_monomial,zsa,mul_pow,zeY,
  zX0]
 change d.support.sum d=n at hdeg
 rw [hdeg]
 ac_rfl
private theorem dch {k T σ:Type} [zrb k] [za6 T] [zZE k T]
  {Q:znc (z3y σ k)} (hQ:Q.IsHomogeneous (homogeneousSubmodule σ k))
  (v :σ→T) (u:T) (h : ∀ p∈Q,aeval v p=0) :
  ∀ p∈Q,aeval (fun j=>u*v j) p=0:= by
 intro p hp
 rw [← sum_homogeneousComponent p,map_sum]
 apply zYF
 intro n _
 rw [aNz v u (homogeneousComponent_isHomogeneous _ _),
  h _ (homogeneousComponent_mem_of_mem hQ hp n),mul_zero]
private theorem gmo {k F T σ:Type} [zrb k] [zrb F] [za6 T]
   [zZE k F] [zZE k T] [zZE F T] [zsf k F T]
   {Q:znc (z3y σ k)} (hQ:Q.IsHomogeneous (homogeneousSubmodule σ k))
   (v :σ→T) (u:T) (h : ∀ p∈Q,aeval v p=0) :
   ∀ p∈Q.map (zDK (algebraMap k F)),
     aeval (R:=F) (fun j=>u*v j) p=0:= by
 let:zsf k F (z3y σ F) :=zsL fun _=>rfl
 let t:z3y σ F →ₐ[F] T:=aeval (fun j=>u*v j)
 let m:z3y σ k →ₐ[k] z3y σ F :=
   zWY (zNX k F)
 have ht: (t.restrictScalars k).comp m=aeval (fun j=>u*v j) := by
   apply zpH
   intro j
   change t (zDK (algebraMap k F) (z9v j)) =
     aeval (R:=k) (fun l=>u*v l) (z9v j)
   simp only [t,z7N,aeval_X]
 have hle :Q.map (zDK (algebraMap k F))≤zdq t.toRingHom:= by
   apply Ideal.map_le_iff_le_comap.mpr
   intro p hp
   change ((t.restrictScalars k).comp m) p=0
   rw [ht]
   exact dch hQ v u h p hp
 exact fun p hp=>hle hp
private abbrev bY {k σ:Type} [zrb k] (Q:znc (z3y σ k)) (i:σ) :=
 z3y σ k ⧸ (Q ⊔ zye {z9v i - 1})
private def eGN {k F σ:Type} [zrb k] [zrb F] [zZE k F]
  (Q:znc (z3y σ k)) (i:σ) (a :bY Q i) (j:σ) :
  F ⊗[k] Localization.Away a :=
 zgi (R:=k)
  (algebraMap (bY Q i) (Localization.Away a) (zVv _ (z9v j)))
private theorem recover {k F σ:Type} [zrb k] [zrb F] [zZE k F]
    (Q:znc (z3y σ k)) (i:σ) (a :bY Q i)
    (hQ:Q.IsHomogeneous (homogeneousSubmodule σ k))
    [ztn (bY Q i)] (ha :a≠0)
    [ztn (F ⊗[k] Localization.Away a)]
    [ztn (z3y σ F ⧸ Q.map (zDK (algebraMap k F)))] :
    ∃ e :FractionRing (z3y σ F ⧸ Q.map (zDK (algebraMap k F))) ≃ₐ[F]
        FractionRing ((F ⊗[k] Localization.Away a)[X]),
      ∀ j:σ,
        e (aFR.asz (z3y σ F ⧸ Q.map (zDK (algebraMap k F)))
          (zVv _ (z9v j))) =
        aFR.asz ((F ⊗[k] Localization.Away a)[X])
          (z1z (eGN (F:=F) Q i a j)*z7y) := by
  classical
  let I:znc (z3y σ k) := Q ⊔ zye {z9v i - 1}
  let J:znc (z3y σ F) := Q.map (zDK (algebraMap k F))
  let A:=bY Q i
  let L:=Localization.Away a
  let B:=F ⊗[k] L
  let R:=z3y σ F ⧸ J
  let E :=FractionRing R
  let D:=FractionRing B[X]
  let:ztn B := ‹ztn (F ⊗[k] Localization.Away a)›
  let:zrb E :=FractionRing.field (A:=R)
  let:zrb D:=FractionRing.field (A:=B[X])
  let:zsf k F (z3y σ F) :=zsL fun _=>rfl
  let:zsf k F B[X] :=zsL fun _=>rfl
  let:zsf k F E :=zsL fun _=>rfl
  let:zsf k F D:=zsL fun _=>rfl
  let π:z3y σ k →ₐ[k] A:=zvR k I
  let q:z3y σ F →ₐ[F] R:=zvR F J
  let m:z3y σ k →ₐ[k] z3y σ F :=
    zWY (zNX k F)
  let b₀:A →ₐ[k] L:=zE2 k A L
  let b₁:L →ₐ[k] B:=zgi
  let b:=b₁.comp b₀
  let jE :R →ₐ[F] E :=zE2 F R E
  let jD:B[X] →ₐ[F] D:=zE2 F B[X] D
  let Ck :B →ₐ[k] B[X] :=z97
  let w (j:σ) :B[X] :=z1z (b (π (z9v j)))
  let z (j:σ) :R:=q (z9v j)
  have hπi:π (z9v i)=1 :=sub_eq_zero.mp (by
    rw [← map_one π,← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show zye {z9v i - 1} ≤ I from le_sup_right)
        (z5J (z9v i - 1))))
  have hw:aeval w=Ck.comp (b.comp π) := by
    apply zpH
    intro j
    exact aeval_X _ _
  let t:z3y σ F →ₐ[F] B[X] :=aeval (fun j=>z7y*w j)
  have hwQ : ∀ p∈Q,aeval w p=0:= by
    intro p hp
    have hπ:π p=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((show Q≤I from le_sup_left) hp)
    rw [hw,zip,zip,hπ,map_zero,map_zero]
  have htJ : ∀ p∈J,t p=0 :=
    gmo (F:=F) (T:=B[X]) hQ w z7y hwQ
  let φ:R →ₐ[F] B[X] :=zTA J t htJ
  have hφ (j:σ) :φ (z j)=z7y*w j:=aeval_X _ _
  have hφi:φ (z i)=Polynomial.X:= by
    rw [hφ]
    simp [w,hπi]
  have hscaleD:jD z7y≠0:= by
    intro h
    exact z05 ((zxb B[X] D) (h.trans (map_zero jD).symm))
  have hz :jE (z i)≠0:= by
    intro h
    have hzero :z i=0:=(zxb R E) (h.trans (map_zero jE).symm)
    exact z05 (hφi.symm.trans ((congrArg φ hzero).trans (map_zero φ)))
  let V:=Localization.Away (z i)
  let:zsf k F V:=zsL fun _=>rfl
  let ι:R →ₐ[F] V:=zE2 F R V
  let s :V:=IsLocalization.Away.invSelf (z i)
  have hs :ι (z i)*s=1 :=IsLocalization.Away.mul_invSelf (S:=V) (z i)
  let v (j:σ) :V:=s*ι (z j)
  have hv (j:σ) :ι (z i)*v j=ι (z j) := by
    change ι (z i)*(s*ι (z j))= _
    rw [← mul_assoc,hs,one_mul]
  let pV:z3y σ k →ₐ[k] V:=((ι.comp q).restrictScalars k).comp m
  have hpV:aeval (fun j=>ι (z j))=pV:= by
    apply zpH
    intro j
    change aeval (R:=k) (fun l=>ι (z l)) (z9v j) =
      ι (q (zDK (algebraMap k F) (z9v j)))
    rw [aeval_X,z7N]
  have hpVQ : ∀ p∈Q,aeval (R:=k) (fun j=>ι (z j)) p=0:= by
    intro p hp
    have hq:q (zDK (algebraMap k F) p)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (z7X _ hp)
    rw [hpV]
    change ι (q (zDK (algebraMap k F) p))=0
    rw [hq,map_zero]
  have hvI : ∀ p∈I,aeval v p=0:= by
    have hle :I≤zdq (aeval v :z3y σ k →ₐ[k] V).toRingHom:= by
      refine sup_le (dch hQ (fun j=>ι (z j)) s hpVQ) (Ideal.span_le.mpr ?_)
      intro p hp
      obtain rfl :=Set.mem_singleton_iff.mp hp
      change aeval (R:=k) v (z9v i - 1)=0
      rw [map_sub,aeval_X,map_one,sub_eq_zero]
      exact (mul_comm _ _).trans hs
    exact fun p hp=>hle hp
  let α:A →ₐ[k] V:=zTA I (aeval v) hvI
  have hα (j:σ) :α (π (z9v j))=v j:=aeval_X _ _
  have hunitE :IsUnit (jE (z i)) :=isUnit_iff_ne_zero.mpr hz
  let ρ:V →ₐ[F] E :=zHH (z i) (f :=jE) hunitE
  have hρ (x :R) :ρ (ι x)=jE x :=
    zaz (S:=V) (g:=jE.toRingHom) (z i) hunitE x
  have hunitD:IsUnit ((jD.comp φ) (z i)) :=isUnit_iff_ne_zero.mpr (by
    change jD (φ (z i))≠0
    rwa [hφi])
  let τ:V →ₐ[F] D:=zHH (z i) (f :=jD.comp φ) hunitD
  have hτ (x :R) :τ (ι x)=jD (φ x) :=
    zaz (S:=V) (g:=(jD.comp φ).toRingHom) (z i) hunitD x
  have hτv (j:σ) :τ (v j)=jD (w j) := by
    have ht1 :τ (ι (z i))*τ (v j)=τ (ι (z j)) := by rw [← map_mul,hv]
    rw [hτ (z i),hτ (z j),hφi,hφ j,map_mul jD] at ht1
    exact mul_left_cancel₀ hscaleD ht1
  let Jk :=jD.restrictScalars k
  have hτα: (τ.restrictScalars k).comp α=Jk.comp (Ck.comp b) := by
    apply zoA k
    apply zpH
    intro j
    change τ (α (π (z9v j)))=jD (w j)
    rw [hα,hτv]
  have hb₀:zq4 b₀ :=
    zHp L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hb₁:zq4 b₁ :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k F).injective
  have hαa :α a≠0:= by
    intro h
    have he :=zmU hτα a
    change τ (α a)=jD (z1z (b₁ (b₀ a))) at he
    rw [h,map_zero] at he
    have hinj:=(zxb B[X] D).comp
      (Polynomial.C_injective.comp (hb₁.comp hb₀))
    apply ha
    apply hinj
    change jD (z1z (b₁ (b₀ a)))=jD (z1z (b₁ (b₀ 0)))
    rw [he.symm,map_zero,map_zero,map_zero,map_zero]
  have hinjρ:zq4 ρ:= by
    apply IsLocalization.injective_of_map_algebraMap_zero (M:=zSL (z i))
      V ρ.toRingHom
    intro x hx
    change ρ (ι x)=0 at hx
    rw [hρ] at hx
    have hx' : x=0:=(zxb R E) (hx.trans (map_zero jE).symm)
    change ι x=0
    rw [hx',map_zero]
  let rA:A →ₐ[k] E :=(ρ.restrictScalars k).comp α
  have hunitA:IsUnit (rA a) :=isUnit_iff_ne_zero.mpr (by
    change ρ (α a)≠0
    intro h
    exact hαa (hinjρ (h.trans (map_zero ρ).symm)))
  let gL:L →ₐ[k] E :=zHH a (f :=rA) hunitA
  let gB:B →ₐ[F] E :=(zuh k F L E) gL
  have hgB (x :L) :gB (b₁ x)=gL x := by
    change (zuh k F L E gL) (1 ⊗ₜ[k] x)= _
    simp
  let g:B[X] →ₐ[F] E :=Polynomial.aevalTower gB (jE (z i))
  have hgX:g z7y=jE (z i) :=Polynomial.aevalTower_X _ _
  have hgC (x :B) :g (z1z x)=gB x :=Polynomial.aevalTower_C _ _ _
  have hgchart (x :A) :gB (b x)=ρ (α x) := by
    change gB (b₁ (b₀ x))= _
    rw [hgB]
    exact zaz (S:=L) (g:=rA.toRingHom) a hunitA x
  have hgφ:g.comp φ=jE := by
    apply zoA F
    apply zpH
    intro j
    change g (φ (z j))=jE (z j)
    rw [hφ,map_mul,hgX]
    change jE (z i)*g (z1z (b (π (z9v j))))= _
    rw [hgC,hgchart,hα,← hρ,← map_mul,hv,hρ]
  have hinj:zq4 (jD.comp φ) := by
    apply (zxb B[X] D).comp
    intro x y h
    apply zxb R E
    exact (zmU hgφ x).symm.trans
      ((congrArg g h).trans (zmU hgφ y))
  let f :E →ₐ[F] D:=zeU (K:=E) (L:=D) (g:=jD.comp φ) hinj
  have hf (x :R) :f (jE x)=jD (φ x) :=
    zoc (K:=E) (g:=(jD.comp φ).toRingHom) hinj x
  have hfρ:f.comp ρ=τ:= by
    apply zst
    apply zuW (zSL (z i))
    apply zz4
    intro x
    change f (ρ (ι x))=τ (ι x)
    rw [hρ,hτ,hf]
  have hfgB:f.comp gB=jD.comp (z97:B →ₐ[F] B[X]) := by
    apply Algebra.TensorProduct.ext_ring (R:=k)
    apply zst
    apply zuW (zSL a)
    apply zz4
    intro x
    change f (gB (b x))=jD (z1z (b x))
    rw [hgchart]
    exact (zmU hfρ (α x)).trans (zmU hτα x)
  have hfg:f.comp g=jD:= by
    apply Polynomial.algHom_ext'
    · apply zjT
      intro x
      change f (g (z1z x))=jD (z1z x)
      rw [hgC]
      exact zmU hfgB x
    · change f (g z7y)=jD z7y
      rw [hgX,hf,hφi]
  have hsurj:zpX f := by
    intro y
    obtain ⟨p,q,_,rfl⟩:=zJC B[X] y
    refine ⟨g p/g q,?_⟩
    rw [map_div₀]
    exact congrArg₂ (· / ·) (zmU hfg p) (zmU hfg q)
  let e :=AlgEquiv.ofBijective f ⟨f.injective,hsurj⟩
  refine ⟨e,fun j => ?_⟩
  change f (jE (z j))=jD (w j*z7y)
  rw [hf,hφ]
  exact congrArg jD (mul_comm (z7y:B[X]) (w j))
open aR B7 Ey Pw aFR
theorem proof :aFR.c1 := by
 intro Q i a hQ hhom _ hchart ha hopen
 have hsource :ztn (mK ⧸ oV Q) :=
  (zMn _).mpr (bqp Q hQ)
 exact @recover ao dF rS _ _ _ Q i a hhom hchart ha hopen hsource
end
end cx3
end
section
namespace ap5
open B7
noncomputable section
def adF:mK:=KT PV 0
def aAE (Q:znc jo) :znc mK :=
 oV Q ⊔ zye {adF}
def biv (Q:znc jo) (i:rS) :znc mK :=
 aAE Q ⊔ zye {z9v i - 1}
end
end ap5
end
section
namespace ap5
open aR B7 Pw MvPolynomial
open scoped Polynomial TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
section ScalarExtension
variable {k F σ:Type*} [zrb k] [zrb F] [zZE k F]
private def Pd (I:znc (z3y σ k)) :
   F ⊗[k] (z3y σ k ⧸ I) ≃ₐ[F]
     z3y σ F ⧸ I.map (zDK (algebraMap k F)) := by
 let e :=zoR (σ:=σ) k F
 let ι:z3y σ k →ₐ[k] F ⊗[k] z3y σ k :=zgi
 have he :e.toRingHom.comp ι.toRingHom=zDK (algebraMap k F) := by
   apply zz4
   intro p
   change e (1 ⊗ₜ[k] p)= _
   simp [e]
 refine (zTd (R:=k) F _ F I).trans
   (zpY _ _ e ?_)
 exact ((z0L (I:=I) ι.toRingHom e.toRingHom).trans
   (congrArg (fun f=>I.map f) he)).symm
private theorem aWG (I:znc (z3y σ k)) (c:F)
  (p:z3y σ k) :
  Pd I (c ⊗ₜ[k] (zVv I p)) =
    c•zVv _ (zDK (algebraMap k F) p) := by
 simp only [Pd,AlgEquiv.trans_apply,zTe,
  Ideal.quotientEquivAlg_mk,MvPolynomial.algebraTensorAlgEquiv_tmul]
 exact (zvR F _).toLinearMap.map_smul c _
end ScalarExtension
abbrev bQ0 (Q:znc jo) (i:rS) :=
 dF ⊗[ao] ChartRing Q i
def alG (Q:znc jo) (i:rS) :bQ0 Q i :=
 V5 _ (direction Q i)
def bcq (Q:znc jo) (i:rS) :
    mK →ₐ[dF] bQ0 Q i :=
  zIe fun j:rS =>
    (1 :dF) ⊗ₜ[ao] (zVv
      (Q ⊔ zye {z9v i - 1}) (z9v j) :ChartRing Q i)
private def aQM (Q:znc jo) (i:rS) :
  bQ0 Q i ≃ₐ[dF]
   mK ⧸ (oV Q ⊔ zye {z9v i - 1}) := by
 refine (Pd (Q ⊔ zye {z9v i - 1})).trans ?_
 apply z9k dF
 simp [oV,zXe,zlN]
private theorem dg4 (Q:znc jo) (i:rS)
  (c:dF) (p:jo) :
  aQM Q i (c ⊗ₜ[ao]
    (zVv (Q ⊔ zye {z9v i - 1}) p)) =
    c•zVv _ (zDK (algebraMap ao dF) p) := by
 simp only [aQM,AlgEquiv.trans_apply,aWG,map_smul,
  zeu]
private theorem cs8 (Q:znc jo) (i:rS)
  (p:mK) :
  aQM Q i (bcq Q i p)=zVv _ p:= by
 have he : (aQM Q i).toAlgHom.comp (bcq Q i) =
    Ideal.Quotient.mkₐ dF _:= by
  apply zpH
  intro j
  rw [zip,bcq,aeval_X]
  change aQM Q i (1 ⊗ₜ[ao] (zVv _ (z9v j))) =
    zVv _ (z9v j)
  rw [dg4 Q i,one_smul,z7N]
 exact AlgHom.congr_fun he p
private theorem d2g {k F A σ:Type} [zrb k] [zrb F] [za6 A]
    [zZE k F] [zZE k A] [z85 σ] (z :F) (d:σ→ℕ) (a :σ→A) :
    (zqf Algebra.TensorProduct.includeRight.toRingHom
      (algebraMap F (F ⊗[k] A) z)) (∑ j,zdM (d j) (a j)) =
      zIe (fun j=>(1 :F) ⊗ₜ[k] a j)
        (∑ j,znf (z^d j)*z9v j) := by
  rw [map_sum,map_sum]
  apply zUo rfl
  intro j _
  rw [z4Q,zFK,map_mul,aeval_C,aeval_X,map_pow]
  exact mul_comm _ _
private theorem dIh (Q:znc jo) (i:rS) :
   bcq Q i adF=alG Q i:= by
 have h:adF =
     ∑ j:rS,znf (PV^j.val)*z9v j:= by
   simp only [adF,KT,zCM,z4o,one_mul,Nat.sub_zero]
 rw [h]
 exact (d2g PV Fin.val (fun j:rS =>
   (zVv (Q ⊔ zye {z9v i - 1}) (z9v j) :
     ChartRing Q i))).symm
theorem cFd (Q:znc jo) (i:rS) :
  aQM Q i (alG Q i)=zVv _ adF:= by
 rw [← dIh,cs8]
theorem ed7 (Q:znc jo) (i:rS)
  (hnonzero :alG Q i≠0) :adF∉oV Q:= by
 intro h
 apply hnonzero
 apply (aQM Q i).injective
 rw [cFd,map_zero,z1Q]
 exact zKg h
private theorem dHW {k :Type} [zrb k] {n:ℕ}
  (Q:znc (z3y (Fin n) k)) (i:Fin n) :
  (zVv _ (z9v i) :yI Q i)=1 := by
 apply sub_eq_zero.mp
 rw [← map_one (zVv _),← map_sub,z1Q]
 exact zs0 (z5J _)
private theorem dH0 {k :Type} [zrb k] {n:ℕ}
   (Q:znc (z3y (Fin n) k)) (i:Fin n) :
   (ayi Q i).coeff i.val=1 := by
 classical
 rw [ayi,zaW,zi6 i]
 · rw [z2j,dHW]
 · intro j _ hji
   simp [zQm,Fin.val_ne_of_ne hji]
 · simp
theorem dXh (Q:znc jo) (i:rS) [ztn (ChartRing Q i)] :
  direction Q i≠0:= by
 intro h
 have hc:=dH0 Q i
 change ayi Q i=0 at h
 rw [h,zO6] at hc
 exact zero_ne_one hc
section Principal
variable {F A B:Type} [za6 F] [za6 A] [za6 B] [zZE F A] [zZE F B]
def ccH (e :A ≃ₐ[F] B) {x :A} {y :B} (h:e x=y) :
    SH x ≃ₐ[F] SH y :=
  zpY _ _ e (by
    rw [zlN,zyk]
    change zye {y} = zye {e x}
    rw [h])
@[simp]
theorem eOr (e :A ≃ₐ[F] B) {x :A} {y :B} (h:e x=y) (z :A) :
 ccH e h (zVv _ z)=zVv _ (e z) :=rfl
private def c5n (I:znc A) (x :A) :
   SH (zVv I x) ≃ₐ[F] A ⧸ (I ⊔ zye {x}) :=
 (z9k F (show zye {zVv I x} =
   (zye {x}).map (zvR F I) by
     rw [zlN,zyk,Ideal.Quotient.mkₐ_eq_mk])).trans
   (DoubleQuot.quotQuotEquivQuotSupₐ F I (zye {x}))
@[simp]
private theorem eOq (I:znc A) (x p:A) :
 c5n (F:=F) I x (zVv _ (zVv I p)) =
  Ideal.Quotient.mk _ p:=rfl
end Principal
def bys (Q:znc jo) (i:rS) :
    SH (alG Q i) ≃ₐ[dF] mK ⧸ biv Q i :=
  (ccH (aQM Q i) (cFd Q i)).trans
    ((c5n _ adF).trans
      (z9k dF (sup_right_comm _ _ _)))
theorem gKV (Q:znc jo) (i:rS) (p:mK) :
  bys Q i (zVv _ (bcq Q i p)) =
   Ideal.Quotient.mk _ p:= by
 simp only [bys,AlgEquiv.trans_apply,eOr,
  cs8,eOq,zeu]
theorem dIe (Q:znc jo) (i:rS) (p:jo) :
   bcq Q i (zDK (algebraMap ao dF) p) =
     (1 :dF) ⊗ₜ[ao] zVv _ p:= by
 apply (aQM Q i).injective
 rw [cs8]
 rw [dg4,one_smul]
end
end ap5
end
section
namespace ap5
open aR B7 Pw
open scoped Polynomial TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
section Localization
variable {F A:Type} [za6 F] [za6 A] [zZE F A]
private def eQr (v b:A)
   (hb:IsUnit (zVv (zye {v}) b)) :
   SH (algebraMap A (Localization.Away b) v) ≃ₐ[F] SH v := by
 let S:=Localization.Away b
 let D:=SH v
 let J:znc S:=zye {algebraMap A S v}
 let q:A →ₐ[F] D:=zvR F _
 let π:S →ₐ[F] S ⧸ J:=zvR F J
 let g:S →ₐ[F] D:=zHH b (show IsUnit (q b) from hb)
 have hg (x :A) :g (algebraMap A S x)=q x :=
   zaz b (g:=q.toRingHom) hb x
 have hv :q v=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (z5J v)
 have hπ:π (algebraMap A S v)=0 :=
   Ideal.Quotient.eq_zero_iff_mem.mpr (z5J _)
 have hJ:J≤zdq g.toRingHom :=
   Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ((hg v).trans hv))
 let forward:A →ₐ[F] S ⧸ J:=π.comp (zE2 F A S)
 have hV:zye {v} ≤ zdq forward.toRingHom :=
   Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ)
 let f :S ⧸ J →ₐ[F] D:=zTA J g (fun _ hx=>hJ hx)
 let r :D →ₐ[F] S ⧸ J:=zTA _ forward (fun _ hx=>hV hx)
 have hf (x :S) :f (π x)=g x :=rfl
 have hr (x :A) :r (q x)=π (algebraMap A S x) :=rfl
 refine AlgEquiv.ofAlgHom f r ?_ ?_
 · apply zjT
   intro x
   obtain ⟨x,rfl⟩:=zld x
   change f (r (q x))=q x
   rw [hr,hf,hg]
 · suffices h:r.comp g=π by
     apply zjT
     intro x
     obtain ⟨x,rfl⟩:=zld x
     change r (f (π x))=π x
     rw [hf]
     exact AlgHom.congr_fun h x
   apply IsLocalization.algHom_ext (zSL b)
   ext x
   change r (g (algebraMap A S x))=π (algebraMap A S x)
   rw [hg,hr]
end Localization
private theorem edY {A B:Type} [za6 A] [za6 B]
  [zZE ao A] [zZE ao B] (f :A →ₐ[ao] B) (p:A[X]) :
  (zv2 (zhD dF dF) f) (V5 A p) =
    V5 B (p.map f.toRingHom) := by
 have h: (zv2 (zhD dF dF) f).toRingHom.comp
    (V5 A)=(V5 B).comp (zhd f.toRingHom) := by
  apply z86
  · intro a
    simp [V5,z4Q,Algebra.TensorProduct.includeRight_apply]
  · simp [V5,z4Q,Algebra.TensorProduct.algebraMap_apply]
 exact zLs h p
private theorem gAW {k F A:Type} [za6 k] [za6 F] [za6 A]
    [zZE k F] [zZE k A] (a :A) (x :F ⊗[k] A) :
    zaF k F a (Localization.Away a)
      ((zv2 (zhD F F)
        (zE2 k A (Localization.Away a))) x) =
      algebraMap (F ⊗[k] A) (Localization.Away ((1 :F) ⊗ₜ[k] a)) x := by
  induction x using z2P with
  | tmul c z =>
    rw [Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
    exact IsLocalization.Away.tensorProductEquivTMulRight_tmul (R:=k) (S:=F) (A:=A) a
      (Localization.Away a) c z
  | add x y hx hy=>simp only [map_add,hx,hy]
def cxF {A:Type} [za6 A] (v b:A) :Prop :=
 IsUnit (zVv (zye {v}) b)
def gKW {A:Type} [za6 A] [zZE ao A] (a :A) (p:A[X])
    (ha :cxF (V5 A p) ((1 :dF) ⊗ₜ[ao] a)) :
    SH (V5 (Localization.Away a) (p.map (algebraMap A _))) ≃ₐ[dF]
      SH (V5 A p) := by
  let B:=Localization.Away a
  let S:=dF ⊗[ao] A
  let b:S:=(1 :dF) ⊗ₜ[ao] a
  let T:=Localization.Away b
  let e :dF ⊗[ao] B ≃ₐ[dF] T :=
    zaF ao dF a B
  let g:=zv2 (zhD dF dF) (zE2 ao A B)
  have he (x :S) :e (g x)=algebraMap S T x :=gAW a x
  have hv :e (V5 B (p.map (algebraMap A B)))=algebraMap S T (V5 A p) := by
    have hf :=edY (zE2 ao A B) p
    change g (V5 A p)=V5 B (p.map (algebraMap A B)) at hf
    rw [← hf,he]
  exact (ccH e hv).trans (eQr _ b ha)
end
end ap5
end
section
namespace axd
noncomputable section
open B7 Ey MvPolynomial
set_option backward.isDefEq.respectTransparency false
def TS {K σ:Type} [zrb K] (I:znc (z3y σ K)) :
    z3y (Option σ) K →ₐ[K] zM1 (z3y σ K ⧸ I) :=
  zIe (R:=K) (S₁:=zM1 (z3y σ K ⧸ I)) fun
    | none=>Polynomial.X
    | some j=>Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.X j))*Polynomial.X
def JA {K σ:Type} [zrb K] (I:znc (z3y σ K)) :
    znc (z3y (Option σ) K) :=
  zdq (TS I).toRingHom
abbrev Closure {K σ:Type} [zrb K] (I:znc (z3y σ K)) :=
 z3y (Option σ) K ⧸ JA I
def Zu {K σ:Type} [zrb K] (I:znc (z3y σ K)) :Closure I :=
 zVv (JA I) (z9v none)
def auA {K σ:Type} [zrb K] (I:znc (z3y σ K))
    (f :z3y σ K) :Closure I :=
  zVv (JA I) (rename some f)
def afp {σ:Type} (L:Fin 2→z3y σ dF)
    (I:znc (z3y σ dF)) :zM1 l5 →+* Closure I :=
  zqf (aeval fun i=>auA I (L i)).toRingHom (Zu I)
def a2z {σ:Type} (L:Fin 2→z3y σ dF)
    (I:znc (z3y σ dF)) :Cardinal :=
  letI:zeq (zM1 l5) (Closure I) :=
    zki (Closure I) (afp L I)
  z1x (zM1 l5) (Closure I)
def aAz (g:nW) :nW :=
 homogeneousComponent g.totalDegree g
end
end axd
end
section
namespace ap5
open aR B7 Pw
open scoped Polynomial TensorProduct nonZeroDivisors
noncomputable section
theorem cS7 (A:Type) [za6 A] [ztn A] [zZE ao A] :
    ztn (dF ⊗[ao] A)∧zq4 (V5 A) := by
  let P:=ao[X]
  let M:=nonZeroDivisors P
  let R:=A ⊗[ao] P
  let ι:P →ₐ[ao] R:=zgi
  let S:=Localization (M.map ι)
  let e :A[X] ≃ₐ[A] R:=polyEquivTensor' ao A
  let:ztn R:=e.symm.toRingEquiv.injective.isDomain _
  have hι:zq4 ι:= by
    have he (p:P) :e.symm (ι p)=p.map (algebraMap ao A) := by
      change (polyEquivTensor ao A).symm ((1 :A) ⊗ₜ[ao] p)= _
      rw [polyEquivTensor_symm_apply_tmul_eq_smul,one_smul]
    intro p q hpq
    exact zTo _ (algebraMap ao A).injective
      ((he p).symm.trans ((congrArg e.symm hpq).trans (he q)))
  have hM:M.map ι≤nonZeroDivisors R:=map_le_nonZeroDivisors_of_injective _ hι le_rfl
  let:ztn S:=IsLocalization.isDomain_localization hM
  let E :=IsLocalization.tensorProductEquivOfMapIncludeRight ao A M dF S
  let E' := (Algebra.TensorProduct.comm ao dF A).toRingEquiv.trans E.toRingEquiv
  have hmap :E'.toRingHom.comp (V5 A)=(algebraMap R S).comp e.toRingHom:= by
    apply z86
    · intro a
      simp only [zQb,V5,z4Q,zJU]
      change E (a ⊗ₜ[ao] (1 :dF))=algebraMap R S (e (z1z a))
      rw [← map_one (algebraMap P dF),
        zL5]
      congr 1
      change a ⊗ₜ[ao] (1 :P)=polyEquivTensor ao A (z1z a)
      rw [polyEquivTensor_apply,zJU]
      rfl
    · simp only [zQb,V5,z4Q,zC9]
      change E ((1 :A) ⊗ₜ[ao] algebraMap P dF z7y) =
        algebraMap R S (e z7y)
      rw [zL5]
      congr 1
      change (1 :A) ⊗ₜ[ao] (z7y:P)=polyEquivTensor ao A z7y
      rw [polyEquivTensor_apply,zC9]
  refine ⟨E'.injective.isDomain _,?_⟩
  have hinj:zq4 (E'.toRingHom.comp (V5 A)) := by
    rw [hmap]
    exact (zHp S hM).comp e.injective
  exact fun _ _ h=>hinj (congrArg E' h)
end
end ap5
end
section
namespace axd
noncomputable section
open B7 Ey MvPolynomial
open scoped Polynomial TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
def c1 :Prop :=
  ∀ g:nW,0<g.totalDegree →
    ∃ L:Fin 2→nW,
      agE L (zye {aAz g}) ∧
      a2z L (zye {g})≤(g.totalDegree :Cardinal)
def c2 :Prop :=
  ∀ (P:znc jo) (g d:nW),XP P g d →
    aAz g∈aVq (oV (adN P)) ∧
    ∃ s :Closure (oV P) →ₐ[dF]
        (mK ⧸ oV (adN P)),
      zpX s ∧
      s (Zu (oV P))=0 ∧
      ∀ f :mK,
        s (auA (oV P) f) =
          zVv (oV (adN P)) f
def c3:Prop :=
  ∀ (P:znc jo) (g d:nW),XP P g d →
    ∃ s :Closure (zye {g}) →ₐ[dF] Closure (oV P),
      s (Zu (zye {g}))=Zu (oV P) ∧
      (∀ f :nW,
        s (auA (zye {g}) f)=auA (oV P) (tO f)) ∧
      ∃ b:Closure (zye {g}),s b≠0 ∧
        ∀ a :Closure (oV P),∃ q:Closure (zye {g}),∃ m:ℕ,
          s q=s b^m*a
private theorem dLU {K σ:Type} [zrb K] (I:znc (z3y σ K))
  (hI:I.IsPrime) :Zu I≠0:= by
 intro hw
 have hm:=(z1Q).mp hw
 have hz :TS I (z9v none)=0:=hm
 simp [TS] at hz
private theorem gtO {σ:Type}
    (L:Fin 2→z3y σ dF) (I J:znc (z3y σ dF))
    (s :Closure I →ₐ[dF] (z3y σ dF ⧸ J))
    (hw:s (Zu I)=0)
    (hc : ∀ f,s (auA I f)=zVv J f) :
    s.toRingHom.comp (afp L I) =
      ((zvR dF J).comp (aeval L)).toRingHom.comp
        (zhy 0) := by
  let α:l5 →ₐ[dF] Closure I:=aeval fun i=>auA I (L i)
  let β:l5 →ₐ[dF] (z3y σ dF ⧸ J) :=
    (zvR dF J).comp (aeval L)
  have hcomp:s.comp α=β:= by
    ext i
    simpa [α,β] using hc (L i)
  have heval (r :l5) :s (α r)=β r :=zmU hcomp r
  apply z86
  · intro r
    simpa [afp,α,β] using heval r
  · simpa [afp] using hw
private theorem fU3
   (L:Fin 2→nW) (I:znc nW) (J:znc mK)
   (s :Closure I →ₐ[dF] Closure J) (hw:s (Zu I)=Zu J)
   (hc : ∀ f :nW,s (auA I f)=auA J (tO f)) :
   s.toRingHom.comp (afp L I) =
     afp (fun i=>tO (L i)) J:= by
 let α:l5 →ₐ[dF] Closure I:=aeval fun i=>auA I (L i)
 let β:l5 →ₐ[dF] Closure J:=aeval fun i=>auA J (tO (L i))
 have hcomp:s.comp α=β:= by
   ext i
   simpa [α,β] using hc (L i)
 apply z86
 · intro r
   simpa [afp,α,β] using zmU hcomp r
 · simpa [afp] using hw
private theorem dLX {σ τ:Type}
  (L:Fin 2→z3y σ dF) (L' : Fin 2→z3y τ dF)
  (I:znc (z3y σ dF)) (J:znc (z3y τ dF))
  (hJ: (JA J).IsPrime) (t:Closure I →+* Closure J)
  (hcomp:t.comp (afp L I)=afp L' J)
  (b:Closure I) (hb:t b≠0)
  (hrec : ∀ a :Closure J,∃ q:Closure I,∃ m:ℕ,t q=t b^m*a) (n:ℕ) :
  a2z L I≤(n:Cardinal)→a2z L' J≤(n:Cardinal) := by
 let:ztn (Closure J) :=Ideal.Quotient.isDomain (JA J)
 unfold a2z
 exact fTh (R:=zM1 l5) (A:=Closure I) (B:=Closure J)
  (afp L I) (afp L' J) t hcomp b hb hrec n
private theorem ef2 (R K V:Type) [za6 R] [ztn R]
  [zrb K] [zZE R K] [z0o R K] [AddCommGroup V] [zeq R V]
  (n:ℕ) (hrank :z1x R V≤(n:Cardinal)) :
  zAa K (K ⊗[R] V)∧zsE K (K ⊗[R] V)≤n:= by
 have hfiber :z1x K (K ⊗[R] V)≤(n:Cardinal) :=
  (TensorProduct.isBaseChange R V K).rank_eq.le.trans hrank
 refine ⟨Module.rank_lt_aleph0_iff.mp (hfiber.trans_lt Cardinal.natCast_lt_aleph0),?_⟩
 simpa [zsE] using Cardinal.toNat_le_toNat hfiber Cardinal.natCast_lt_aleph0
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :Ey.c3:= by
 intro P g d hchart
 have hpos :0<g.totalDegree := by
   by_contra! h
   have ha :=totalDegree_eq_zero_iff_eq_C.mp (za7 h)
   have ha0:g.coeff 0≠0:= fun e=>hchart.equation_ne (by simpa [e] using ha)
   have hunit :IsUnit g:= by
     rw [ha]
     exact (isUnit_iff_ne_zero.mpr ha0).map znf
   exact hchart.regular_open (by simp [Ideal.span_singleton_eq_top.mpr hunit])
 obtain ⟨L,hL,hLrank⟩:=h1 g hpos
 obtain ⟨htop,s,hsurj,hw,hc⟩:=h2 P g d hchart
 refine ⟨L,hL.of_le ((Ideal.span_singleton_le_iff_mem _).mpr htop),?_⟩
 let I:=oV P
 let J:=oV (adN P)
 let L' : Fin 2→mK:= fun i=>tO (L i)
 let:I.IsPrime :=bqp P hchart.prime
 have hprime : (JA I).IsPrime :=zgL (TS I).toRingHom
 have hwne :afp L' I z7y≠0:= by
   simpa [afp] using dLU I (inferInstance :I.IsPrime)
 have hs :s.toRingHom.comp (afp L' I) =
     (aWi L J).toRingHom.comp (zhy 0) := by
   have hpair : (zvR dF J).comp (aeval L')=aWi L J:= by
     ext i
     simp [L',aWi]
   rw [← hpair]
   exact gtO L' I J s hw hc
 obtain ⟨t,htw,htc,b,hb,hrec⟩:=h3 P g d hchart
 have hcomp:t.toRingHom.comp (afp L (zye {g})) =
     afp L' I:=fU3 L _ I t htw htc
 have hr :a2z L' I≤(g.totalDegree :Cardinal) :=
   dLX L L' (zye {g}) I hprime t.toRingHom
     hcomp b hb hrec g.totalDegree hLrank
 let B:=mK ⧸ J
 letI:zeq l5 B:=zki B (aWi L J).toRingHom
 have hbrank :z1x l5 B≤(g.totalDegree :Cardinal) := by
   exact fTi (R:=l5) (A:=Closure I) (B:=B)
     (afp L' I) (aWi L J).toRingHom s.toRingHom hwne hs hsurj g.totalDegree hr
 change zAa MY (MY ⊗[l5] B) ∧
   zsE MY (MY ⊗[l5] B)≤g.totalDegree
 exact ef2 l5 MY B g.totalDegree hbrank
end
end axd
end
section
namespace ap5
noncomputable section
open aR B7 Pw MvPolynomial
open scoped Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
def c1 :Prop :=
  ∀ (I:znc jo),
    I.IsHomogeneous (homogeneousSubmodule rS ao) →
    (affineHilbertPolynomial I).natDegree≤1 →
    ∀ j:rS,z9v j∈(aAE I).radical
def c2 :Prop :=
  ∀ {F σ:Type} [zrb F] [Finite σ] (I:znc (z3y σ F)) (ℓ:z3y σ F),
    I.IsHomogeneous (homogeneousSubmodule σ F) →
    (affineHilbertPolynomial I).natDegree=2 →
    ℓ.IsHomogeneous 1→ IsLeftRegular (zVv I ℓ) →
    affineHilbertPolynomial (I ⊔ zye {ℓ}) =
      zW9 1 (affineHilbertPolynomial I)
def c3:Prop :=
  ∀ {F σ:Type} [zrb F] [Finite σ] (I:znc (z3y σ F)) (i:σ),
    I.IsHomogeneous (homogeneousSubmodule σ F) →
    (affineHilbertPolynomial I).natDegree=1 →
    (∀ j:σ,z9v j∈(I ⊔ zye {z9v i}).radical) →
    affineHilbertPolynomial (I ⊔ zye {z9v i - 1}) =
      z1z (affineHilbertPolynomial I).leadingCoeff
private theorem crU {F σ:Type*} [zrb F]
  {I:znc (z3y σ F)} {f :z3y σ F} {d:ℕ}
  (hI:I.IsHomogeneous (homogeneousSubmodule σ F)) (hf :f.IsHomogeneous d) :
  (I ⊔ zye {f}).IsHomogeneous (homogeneousSubmodule σ F) := by
 apply hI.sup
 apply zqZ
 rintro _ ⟨⟩
 exact ⟨d,hf⟩
private theorem ey0 {F E σ:Type*} [zrb F] [zrb E]
  {I:znc (z3y σ F)} (f :F →+* E)
  (hI:I.IsHomogeneous (homogeneousSubmodule σ F)) :
  (I.map (zDK f)).IsHomogeneous (homogeneousSubmodule σ E) := by
 obtain ⟨S,hS⟩:=(Ideal.IsHomogeneous.iff_exists _ I).mp hI
 rw [hS,zlN]
 apply zqZ
 rintro _ ⟨_,⟨q,_,rfl⟩,rfl⟩
 obtain ⟨d,hd⟩:=q.property
 exact ⟨d,(show ((q:z3y σ F)).IsHomogeneous d from hd).map f⟩
private theorem aDK {F σ:Type} [zrb F] [z85 σ] (c:σ→F) :
   (∑ i:σ,znf (c i)*z9v i).IsHomogeneous 1 :=
 (homogeneousSubmodule σ F 1).sum_mem fun i _=>isHomogeneous_C_mul_X _ i
private theorem cTc:adF.IsHomogeneous 1 :=
 aDK (fun i:rS =>
  (i.val.choose 0:dF)*PV^(i.val - 0))
private theorem cSz {Q:znc jo} (hQ:Q.IsPrime)
  (hd: (affineHilbertPolynomial Q).natDegree=2) {g:jo} (hg:g∉Q) :
  (affineHilbertPolynomial (Q ⊔ zye {g})).natDegree≤1 := by
 simpa [hd] using
  (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime hQ hg
    (b:=g.totalDegree) le_rfl).1
private theorem aUr (Q:znc jo) (i:rS)
    (a :ChartRing Q i) :
    ∃ (g:jo) (d:ℕ),g.IsHomogeneous d∧zVv _ g=a := by
  classical
  let J:znc jo:= Q ⊔ zye {z9v i - 1}
  obtain ⟨p,hp⟩:=zld (I:=J) a
  let d:=p.totalDegree
  have hi:zVv J (z9v i)=1 := by
    apply sub_eq_zero.mp
    rw [← (zVv J).map_one,← map_sub,z1Q]
    exact zs0 (z5J _)
  refine ⟨∑ n∈z4x (d+1),z9v i^(d - n)*homogeneousComponent n p,
    d,IsHomogeneous.sum _ _ _ ?_,?_⟩
  · intro n hn
    have hnd:n≤d:=zeh (Finset.mem_range.mp hn)
    simpa only [zxt hnd] using
      (isHomogeneous_X_pow (R:=ao) i (d - n)).mul
        (homogeneousComponent_isHomogeneous n p)
  · change zVv J _=a
    rw [map_sum]
    simp only [map_mul,map_pow,hi,one_pow,one_mul]
    rw [← map_sum,sum_homogeneousComponent,hp]
private theorem dWg (h1 :c1) (Q:znc jo) (i:rS)
   (a :ChartRing Q i) (hQ:Q.IsPrime)
   (hhom:Q.IsHomogeneous (homogeneousSubmodule rS ao))
   (hd: (affineHilbertPolynomial Q).natDegree=2) (ha :a≠0) :
   cxF (alG Q i) ((1 :dF) ⊗ₜ[ao] a) := by
 obtain ⟨g,d,hghom,hg⟩:=aUr Q i a
 have hgQ:g∉Q:= by
   intro h
   apply ha
   rw [← hg,z1Q]
   exact zKg h
 let J:=biv Q i
 let p:=zDK (algebraMap ao dF) g
 let B:znc mK:=J ⊔ zye {p}
 have hle :aAE (Q ⊔ zye {g})≤B:= by
   have h:oV (Q ⊔ zye {g})=oV Q ⊔ zye {p} := by
     simp [oV,p,zXe,zlN]
   rw [aAE,h]
   apply sup_le (sup_le ?_ le_sup_right) ?_
   · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
   · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
 obtain ⟨n,hn⟩:=Ideal.mem_radical_iff.mp
   (h1 (Q ⊔ zye {g}) (crU hhom hghom)
     (cSz hQ hd hgQ) i)
 have hi:zVv B (z9v i)=1 := by
   apply sub_eq_zero.mp
   rw [← (zVv B).map_one,← map_sub,z1Q]
   exact zKg (zs0 (z5J _))
 have hzero :zVv B (z9v i^n)=0 :=
   Ideal.Quotient.eq_zero_iff_mem.mpr (hle hn)
 rw [map_pow,hi,one_pow] at hzero
 have htop:B = ⊤ := (zhc B).mpr
   (Ideal.Quotient.eq_zero_iff_mem.mp ((zVv B).map_one.trans hzero))
 have hspan: (zye {zVv J p} : znc (mK ⧸ J)) = ⊤ := by
   have hm:=congrArg (fun H :znc mK=>H.map (zVv J)) htop
   simpa [B,zXe,zlN,Ideal.map_quotient_self,Ideal.map_top] using hm
 have hunit :=(Ideal.span_singleton_eq_top (x :=zVv J p)).mp hspan
 have he :=gKV Q i p
 rw [dIe,hg] at he
 have hu:=IsUnit.map (bys Q i).symm.toRingHom hunit
 change IsUnit ((bys Q i).symm (zVv J p)) at hu
 rwa [← he,AlgEquiv.symm_apply_apply] at hu
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :Pw.c1 := by
  intro Q i a hQ hhom hd hi hchart ha
  let:ztn (ChartRing Q i) :=hchart
  let:ztn (TC Q i a) :=Localization.Away.isDomain ha
  obtain ⟨hfresh,heval⟩:=cS7 (TC Q i a)
  refine ⟨hfresh,heval,?_⟩
  have hvalue :adF∉oV Q:=ed7 Q i (by
    intro h
    apply dXh Q i
    exact (cS7 (ChartRing Q i)).2 (h.trans (map_zero _).symm))
  have hp:=Ey.bqp Q hQ
  let: (oV Q).IsPrime :=hp
  have hregular :IsLeftRegular (zVv (oV Q) adF) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hvalue)
  have hh: (oV Q).IsHomogeneous (homogeneousSubmodule rS dF) :=
    ey0 (algebraMap ao dF) hhom
  have hvalhom: (aAE Q).IsHomogeneous (homogeneousSubmodule rS dF) :=
    crU hh cTc
  have hbase :affineHilbertPolynomial (oV Q)=affineHilbertPolynomial Q :=
    Ey.ZI Q
  have hfreshdim: (affineHilbertPolynomial (oV Q)).natDegree=2 := by
    rw [hbase,hd]
  have hpoly :affineHilbertPolynomial (aAE Q) =
      zW9 1 (affineHilbertPolynomial Q) := by
    change affineHilbertPolynomial (oV Q ⊔ zye {adF})= _
    rw [h2 (oV Q) adF hh hfreshdim cTc hregular,hbase]
  obtain ⟨hdegree,hlead⟩:=Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (b:=(1 :ℚ)) one_ne_zero (P:=affineHilbertPolynomial Q) (by omega)
  have hboundary : ∀ j:rS,
      z9v j∈(aAE Q ⊔ zye {z9v i}).radical:= by
    have heq :aAE (Q ⊔ zye {z9v i}) =
        aAE Q ⊔ zye {z9v i} := by
      simp only [aAE,oV,zXe,zlN,zyk,
        z7N]
      exact sup_right_comm _ _ _
    rw [← heq]
    exact h1 _ (crU hhom (isHomogeneous_X ao i)) (cSz hQ hd hi)
  have hchartPoly :affineHilbertPolynomial (biv Q i)=z1z (affineDegree Q) := by
    rw [biv,h3 (aAE Q) i hvalhom
      (by rw [hpoly,hdegree,hd]) hboundary,hpoly,hlead]
    norm_num [affineDegree,hd]
  let V:=mK ⧸ biv Q i
  let:zAa dF V:=moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero
    (by rw [hchartPoly,zti])
  have hfinrank : (zsE dF V:ℚ)=affineDegree Q :=
    Polynomial.C_injective ((affineHilbertPolynomial_eq_C_finrank (biv Q i)).symm.trans hchartPoly)
  let e :=(gKW a (direction Q i) (dWg h1 Q i a hQ hhom hd ha)).trans
    (bys Q i)
  exact ⟨zIV e.symm.toLinearMap e.symm.surjective,
    (congrArg (fun n:ℕ=>(n:ℚ)) e.toLinearEquiv.finrank_eq).trans hfinrank⟩
end
end ap5
end
section
namespace bzZ
noncomputable section
open cu gT DQ Cu XW NS MvPolynomial
open scoped Polynomial
set_option maxHeartbeats 1000000
private theorem eJ5 {n:ℕ} (I:znc (DT n)) (hI:I.IsPrime)
   (hd: (affineHilbertPolynomial I).natDegree≤1) :
   atV (Gu (jY n) I) (a2G n) := by
 let p:Option (Fin n)→DT n:= fun i=>i.elim (-1) z9v
 have hw:z14 L (Qd (n:=n)) := by
   have h:=(MvPolynomial.linearIndependent_X (Option (Fin n)) FX).map'
     (zE2 FX (SourceRing n) (jY n)).toLinearMap
     (LinearMap.ker_eq_bot.mpr (zxb (SourceRing n) (jY n)))
   exact h.restrict_scalars' (R:=L)
 have hp (s :Option (Fin n)) : (p s).totalDegree≤1 := by
   cases s <;> simp [p]
 have h:=c7W I hI p _ hw hp
   (fun b _=>⟨none,by simp [p]⟩)
   (fun b _ hb=>funext fun i=> by simpa [p,(homogeneousComponent_eq_self
     (isHomogeneous_X L i))] using hb (some i)) hd
 simpa [a2G,Fintype.sum_option,p,sub_eq_add_neg,add_comm] using h
private theorem bHQ {k E :Type*} [zrb k] [zrb E] [zZE k E]
  {x :E} (h:Transcendental k x) :
  z14 k (fun j:ℕ=>x^j) := by
 have h' := (Polynomial.basisMonomials k).linearIndependent.map'
  (zEU x).toLinearMap (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp h))
 simpa [Function.comp_def,← zoT] using h'
private def aYl:FX:=algebraMap L[X] FX z7y
private def bJ3 {a b:ℕ} (s :Fin a×Fin b) :aQ :=
 algebraMap FX aQ (aYl^s.2.val)*ek 1^s.1.val
private theorem eHT (a b:ℕ) :
  z14 L (bJ3 (a :=a) (b:=b)) := by
 have hx :Transcendental L aYl :=
  (transcendental_algebraMap_iff (zxb L[X] FX)).2
    (Polynomial.transcendental_X L)
 have hy :Transcendental FX (ek 1) :=
  (transcendental_algebraMap_iff (zxb aZ aQ)).2
    (MvPolynomial.transcendental_X FX 1)
 have hX:=(bHQ hx).comp (fun i:Fin b=>i.val) z0e
 have hY:=(bHQ hy).comp (fun j:Fin a=>j.val) z0e
 apply Fintype.linearIndependent_iff.mpr
 intro c hc s
 have he : ∑ j:Fin a,(∑ i:Fin b,c (j,i)•aYl^i.val)•ek 1^j.val=0:= by
  rw [zsI] at hc
  simpa only [bJ3,zd5,map_sum,map_mul,
    zG3 L FX aQ,zkq,mul_assoc] using hc
 exact (Fintype.linearIndependent_iff.mp hX) (fun i=>c (s.1,i))
  ((Fintype.linearIndependent_iff.mp hY) _ he s.1) s.2
private def aRf {n:ℕ} (f :XO n) :ℕ :=
 (z4x (f.natDegree+1)).sup (fun j=>(f.coeff j).natDegree)+1
private theorem cZc {n:ℕ} (f :XO n) {j:ℕ} (hj:j<f.natDegree+1) :
  (f.coeff j).natDegree<aRf f :=
 zB1 (Finset.le_sup (f := fun j=>(f.coeff j).natDegree) (Finset.mem_range.mpr hj))
private def a4z {n:ℕ} (f :XO n)
   (s :Fin (f.natDegree+1)×Fin (aRf f)) :DT n :=
 (f.coeff s.1.val).coeff s.2.val
private theorem eHQ {n:ℕ} (f :XO n) :
    aIM f = ∑ s :Fin (f.natDegree+1)×Fin (aRf f),
      znf (bJ3 s)*map (algebraMap L aQ) (a4z f s) := by
  let χ: (DT n)[X] →+* N4 n :=
    zqf (map (algebraMap L FX)) (znf aYl)
  let ψ:N4 n →+* z3y (Fin n) aQ :=
    map (algebraMap FX aQ)
  let y :z3y (Fin n) aQ:=znf (ek 1)
  have hC (q:DT n) :ψ (χ (z1z q))=map (algebraMap L aQ) q:= by
    change (map (algebraMap FX aQ))
      ((z1z q).eval₂ (map (algebraMap L FX)) (znf aYl))= _
    rw [zJU,z6Y,← zYY]
  have hX:ψ (χ z7y)=znf (algebraMap FX aQ aYl) := by
    change (map (algebraMap FX aQ))
      (Polynomial.X.eval₂ (map (algebraMap L FX)) (znf aYl))= _
    rw [zC9,map_C]
  have hout :
      f = ∑ j:Fin (f.natDegree+1),z1z (f.coeff j.val)*z7y ^j.val := by
    rw [zdx (fun j=>z1z (f.coeff j)*z7y ^j)]
    exact f.as_sum_range_C_mul_X_pow
  have hin (j:Fin (f.natDegree+1)) :
      ψ (χ (f.coeff j.val)) =
        ∑ i:Fin (aRf f),znf (algebraMap FX aQ (aYl^i.val)) *
          map (algebraMap L aQ) ((f.coeff j.val).coeff i.val) := by
    have hs :f.coeff j.val = ∑ i:Fin (aRf f),
        z1z ((f.coeff j.val).coeff i.val)*z7y ^i.val := by
      rw [zdx (fun i =>
        z1z ((f.coeff j.val).coeff i)*z7y ^i)]
      exact (f.coeff j.val).as_sum_range_C_mul_X_pow' (cZc f j.isLt)
    calc
      _=ψ (χ (∑ i:Fin (aRf f),
          z1z ((f.coeff j.val).coeff i.val)*z7y ^i.val)) :=
        congrArg (ψ ∘ χ) hs
      _ = _:= by
        simp only [map_sum,map_mul,map_pow,hC,hX]
        apply zUo rfl
        intro i _
        exact mul_comm _ _
  change (f.map χ).eval₂ ψ y= _
  rw [zem]
  let ε:=zqf (ψ.comp χ) y
  change ε f= _
  rw [congrArg ε hout,map_sum,zsI]
  apply zUo rfl
  intro j _
  rw [map_mul,map_pow]
  simp only [ε,z4Q,zJU,zC9,
    zQb]
  rw [hin,zkq]
  apply zUo rfl
  intro i _
  simp only [y,← map_pow znf,a4z,bJ3,map_mul]
  ac_rfl
private theorem cFj {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) (i:Fin n) :
    z9v i∈TU A ∨
      ∃ s :Fin (A.equation.natDegree+1)×Fin (aRf A.equation),
        a4z A.equation s-MvPolynomial.X i∈TU A:= by
  obtain ⟨j,k,h⟩:=cGE A i
  by_cases hj:j<A.equation.natDegree+1
  · by_cases hk :k<aRf A.equation
    · exact Or.inr ⟨(⟨j,hj⟩,⟨k,hk⟩),h⟩
    · have hz : (A.equation.coeff j).coeff k=0 :=
        zQl (lt_of_lt_of_le (cZc _ hj) (by omega))
      left
      simpa [hz] using h
  · have hz :A.equation.coeff j=0:=Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    left
    simpa [hz] using h
private theorem dIz {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
  {R:wJ C₀ J g} (A:yI R n)
  (b:Fin n→L) (hb:b∈zeroLocus L (TU A)) :
  ∃ s :Fin (A.equation.natDegree+1)×Fin (aRf A.equation),
    eval b (a4z A.equation s)≠0:= by
 by_contra! h
 have hb0 (i:Fin n) :b i=0:= by
  rcases cFj A i with hi | ⟨s,hs⟩
  · simpa [aeval_eq_eval] using hb _ hi
  · have he :=hb _ hs
    simpa [aeval_eq_eval,h s] using he
 obtain ⟨ℓ,hℓ⟩:=cGD A
 have hnorm:=hb _ hℓ
 simp [aeval_eq_eval,hb0] at hnorm
private theorem dIl {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n)
    (b:Fin n→L) (hb:b∈zeroLocus L (lW (TU A)))
    (h : ∀ s,eval b (homogeneousComponent 1 (a4z A.equation s))=0) :
    b=0:= by
  funext i
  rcases cFj A i with hi | ⟨s,hs⟩
  · have hX:z9v i∈lW (TU A) :=
      zCn ⟨z9v i,1,hi,(totalDegree_X i).le,
        (homogeneousComponent_eq_self (isHomogeneous_X L i)).symm⟩
    simpa [aeval_eq_eval] using hb _ hX
  · have hd: (a4z A.equation s-MvPolynomial.X i).totalDegree≤1 :=
      (totalDegree_sub _ _).trans (max_le (A.degree.2 _ _) (totalDegree_X i).le)
    have he :=hb _ (zCn ⟨_,1,hs,hd,rfl⟩)
    simpa [aeval_eq_eval,homogeneousComponent_eq_self (isHomogeneous_X L i),h s] using he
theorem proof :XW.c1 := by
 intro C₀ _ J g n R A hd
 have hI: (TU A).IsPrime :=zgL _
 refine ⟨eJ5 _ hI hd,?_⟩
 rw [eHQ]
 exact c7W _ hI (a4z A.equation) _
  (eHT _ _) (fun s=>A.degree.2 s.1 s.2)
  (dIz A) (dIl A) hd
end
end bzZ
end
section
set_option maxHeartbeats 600000
namespace czt
noncomputable section
open cu gT DQ Cu XW aFZ
open MvPolynomial
open scoped Polynomial
private theorem bqo {P T:Type*} [za6 P] [zrb T]
  [zZE P T] [z0o P T] (U:Subfield T)
  (h : ∀ p:P,algebraMap P T p∈U) (x :T) :x∈U:= by
 obtain ⟨p,q,_,rfl⟩:=zJC P x
 exact U.div_mem (h p) (h q)
theorem proof :aFZ.c1 := by
  intro C₀ _ J g n R A h
  let:zZE L (oO C₀) :=(zT C₀).toAlgebra
  let:=aww (auB A.coordinate)
    (bnt A.coordinate h)
  intro hfinite
  classical
  let S:=jY n
  let F:=fZ A.coordinate
  let B:=FractionRing F[X]
  let W:=ae7 F n
  let T:=TK F n
  let a :=OX A.coordinate
  let k :W →+* T:=algebraMap W T
  let b:B →+* T:=k.comp znf
  let c:F →+* T:=b.comp ((algebraMap F[X] B).comp z1z)
  let ev :z3y (Fin n) S →ₐ[S] T:=aeval (c ∘ a)
  have hFX (x :FX) :
      algebraMap S T (algebraMap FX S x)=b (RB (algebraMap L F) x) := by
    rw [zG3 FX (SourceRing n) S]
    rw [MvPolynomial.algebraMap_eq,bhm]
    exact congrArg k (eval₂Hom_C _ _ _)
  have hL (x :L) :
      algebraMap S T (algebraMap L S x)=c (algebraMap L F x) := by
    rw [zG3 L FX S,hFX]
    rw [zG3 L L[X] FX,zrE]
    simp only [c,zQb,RB,zJ1,
      zi7,zKC,zrL]
    rfl
  have ev_coeff :
      ev.toRingHom.comp (zDK (algebraMap L S)) =
        c.comp (eval₂Hom (algebraMap L F) a) := by
    apply zXT
    · intro x
      simp only [zQb,zpw,eval₂Hom_C]
      change aeval (R:=S) (c ∘ a) (C (algebraMap L S x))= _
      rw [aeval_C,hL]
    · intro i
      simp only [zQb,z7N,eval₂Hom_X']
      exact aeval_X (R:=S) (c ∘ a) i
  have coeff_compat :
      F.val.toRingHom.comp (eval₂Hom (algebraMap L F) a) =
        eval₂Hom (zT C₀) A.coordinate := by
    apply zXT
    · intro x
      simp only [zQb,eval₂Hom_C]
      rfl
    · intro i
      simp only [zQb,eval₂Hom_X']
      rfl
  have hweight (i:Fin n) :algebraMap S T (Qd (some i))=k (z9v i) := by
    rw [Qd,bhm]
    simp only [auB,pD,eval₂Hom_X',Option.elim_some]
    rfl
  have hoffset :algebraMap S T (Qd (n:=n) none) =
      ∑ i,k (z9v i)*c (a i) := by
    rw [Qd,bhm]
    simp only [auB,pD,eval₂Hom_X',Option.elim_none,
      map_sum,map_mul]
    rfl
  have hcut :
      Gu S (TU A) ⊔ zye {a2G n} ≤
        zdq ev.toRingHom:= by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      have hz :eval₂Hom (algebraMap L F) a p=0:= by
        apply F.val.toRingHom.injective
        rw [map_zero,← zQb,coeff_compat]
        exact RingHom.mem_ker.mp hp
      change (ev.toRingHom.comp (zDK (algebraMap L S))) p=0
      rw [ev_coeff,zQb,hz,map_zero]
    · intro p hp
      obtain rfl :=Set.mem_singleton_iff.mp hp
      change ev (a2G n)=0
      rw [a2G,map_sub,sub_eq_zero,map_sum]
      change _=aeval (R:=S) (c ∘ a) (C (Qd (n:=n) none))
      rw [aeval_C,hoffset]
      apply zUo rfl
      intro i _
      rw [map_mul]
      change aeval (R:=S) (c ∘ a) (C (Qd (some i))) *
        aeval (R:=S) (c ∘ a) (z9v i)= _
      rw [aeval_C,aeval_X,hweight]
      rfl
  let f :aYv A →ₐ[S] T :=
    zTA _ ev (fun p hp=>RingHom.mem_ker.mp (hcut hp))
  refine ⟨f,?_⟩
  let:zAa S f.range :=
    zIV f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  let U:=f.range.toIntermediateField' (IsField.of_isDomain_of_finite S f.range)
  have hcoord (i:Fin n) :c (a i)∈U:= by
    refine (AlgHom.mem_range f).mpr ⟨zVv _ (z9v i),?_⟩
    change ev (z9v i)= _
    exact aeval_X (c ∘ a) i
  let V:Subfield B:=U.toSubfield.comap b
  let D:Subfield F:=V.comap ((algebraMap F[X] B).comp z1z)
  let D' : IntermediateField L (oO C₀) :=
    (D.map F.val.toRingHom).toIntermediateField (fun x =>
      ⟨algebraMap L F x,by
        change c (algebraMap L F x)∈U
        rw [← hL]
        exact U.algebraMap_mem _,rfl⟩)
  have hF:F≤D' := IntermediateField.adjoin_le_iff.mpr (by
    rintro _ ⟨i,rfl⟩
    exact ⟨a i,hcoord i,rfl⟩)
  have hconst (x :F) : (algebraMap F[X] B) (z1z x)∈V:= by
    obtain ⟨y,hy,hyx⟩:=hF x.property
    exact (F.val.toRingHom.injective hyx :y=x) ▸ hy
  have hx :algebraMap F[X] B z7y∈V:= by
    change b (algebraMap F[X] B z7y)∈U
    have he :=hFX (algebraMap L[X] FX z7y)
    simp only [RB,zJ1,zi7,
      zKC,zSo] at he
    rw [← he]
    exact U.algebraMap_mem _
  have hB (x :B) :x∈V:= by
    apply bqo (P:=F[X]) V _ x
    intro p
    induction p using zCU with
    | add p q hp hq =>
      rw [map_add]
      exact V.add_mem hp hq
    | monomial m y =>
      rw [← zoT,map_mul,map_pow]
      exact V.mul_mem (hconst y) (V.pow_mem hx m)
  intro x
  apply (AlgHom.mem_range f).mp
  change x∈U.toSubfield
  apply bqo (P:=W) U.toSubfield _ x
  intro p
  change k p∈U
  induction p using z5i with
  | C y=>exact hB y
  | add p q hp hq =>
    rw [map_add]
    exact U.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul,← hweight]
    exact U.mul_mem hp (U.algebraMap_mem _)
end
end czt
end
section
set_option maxRecDepth 2000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace cx7
noncomputable section
open B7 Ey axd MvPolynomial
open scoped TensorProduct
section ScalarExtension
variable {k E σ ι:Type*} [zrb k] [zrb E] [zZE k E]
private abbrev uZ:z3y σ k →+* z3y σ E :=
 zDK (algebraMap k E)
private def Pd (I:znc (z3y σ k)) :
  E ⊗[k] (z3y σ k ⧸ I) ≃ₐ[E] z3y σ E ⧸ I.map uZ:= by
 let e :=zoR (σ:=σ) k E
 let ι' : z3y σ k →ₐ[k] E ⊗[k] z3y σ k :=
  zgi
 have hcomp:e.toRingHom.comp ι'.toRingHom=uZ:= by
  apply zz4
  intro p
  change e (1 ⊗ₜ[k] p)= _
  simp [e,uZ]
 refine (zTd (R:=k) E _ E I).trans
  (zpY _ _ e ?_)
 exact ((z0L (I:=I) ι'.toRingHom e.toRingHom).trans
  (congrArg (fun f=>I.map f) hcomp)).symm
private theorem aWG (I:znc (z3y σ k))
  (a :E) (p:z3y σ k) :
  Pd I (a ⊗ₜ[k] zVv I p) =
    zVv (I.map uZ) (zoR k E (a ⊗ₜ[k] p)) := by
 simp only [Pd,AlgEquiv.trans_apply,zTe]
 rfl
private def dO [DecidableEq ι] (b:z39 ι k E) (p:z3y σ E) (i:ι) :
  z3y σ k :=
 znu b ((zoR k E).symm p) i
private theorem bnn [DecidableEq ι] (b:z39 ι k E) (p:z3y σ E)
   (i:ι) (d:σ →₀ ℕ) : (dO b p i).coeff d=b.coord i (p.coeff d) := by
 let e :=zoR (σ:=σ) k E
 obtain ⟨t,rfl⟩:=e.surjective p
 simp only [dO,show zoR k E=e from rfl,
   AlgEquiv.symm_apply_apply]
 induction t using z2P with
 | tmul a q =>
   simp only [zy4,e,
     algebraTensorAlgEquiv_tmul,coeff_smul,coeff_map]
   have hs :a•algebraMap k E (q.coeff d)=q.coeff d•a := by
     rw [smul_eq_mul,zd5,mul_comm]
   simp only [hs,map_smul,zVi,smul_eq_mul,mul_comm]
 | add t u ht hu =>
   simp only [map_add,AddMonoidAlgebra.coeff_add,zSs,ht,hu]
private theorem mem_map_iff [DecidableEq ι] (b:z39 ι k E)
    (I:znc (z3y σ k)) (p:z3y σ E) :
    p∈I.map uZ ↔ ∀ i,dO b p i∈I:= by
  let e :=zoR (σ:=σ) k E
  let eI:E ⊗[k] (z3y σ k ⧸ I) ≃ₐ[E] _:=Pd I
  let s :=znu (N :=z3y σ k ⧸ I) b
  obtain ⟨t,rfl⟩:=e.surjective p
  have hc (i:ι) :
      s (eI.symm (zVv (I.map uZ) (e t))) i =
        zVv I (znu b t i) := by
    induction t using z2P with
    | tmul a q =>
      rw [← aWG I a q]
      simp only [eI,AlgEquiv.symm_apply_apply,s,
        zy4]
      exact (map_smul (zvR k I) _ _).symm
    | add t u ht hu =>
      simp only [map_add,zSs,ht,hu]
  simp only [dO,show zoR k E=e from rfl,
    AlgEquiv.symm_apply_apply,← z1Q,← hc]
  constructor
  · intro h i
    simp [h]
  · intro h
    have hz :s (eI.symm (zVv (I.map uZ) (e t)))=0 :=
      Finsupp.ext h
    exact eI.symm.injective (s.injective (hz.trans (by simp)))
private theorem dOz (I:znc (z3y σ k)) {p:z3y σ E}
   (hp:p∈I.map uZ) {n:ℕ} (hn:p.totalDegree≤n) :
   homogeneousComponent n p∈(adN I).map uZ:= by
 classical
 let b:=zz1 k E
 apply (mem_map_iff b _ _).2
 intro i
 have hi:=(mem_map_iff b I p).1 hp i
 have hdeg: (dO b p i).totalDegree≤p.totalDegree := by
   apply zRS
   intro d hd
   rw [zuk,bnn] at hd
   exact MvPolynomial.mem_support_iff.mpr fun h=>hd (by rw [h,map_zero])
 have he :dO b (homogeneousComponent n p) i=homogeneousComponent n (dO b p i) := by
   ext d
   by_cases hd:d.degree=n <;> simp [bnn,coeff_homogeneousComponent,hd]
 rw [he]
 rcases eq_or_lt_of_le (hdeg.trans hn) with h | h
 · refine zCn ⟨dO b p i,hi,?_⟩
   change homogeneousComponent (dO b p i).totalDegree (dO b p i)= _
   rw [h]
 · rw [homogeneousComponent_eq_zero n _ h]
   exact znl _
end ScalarExtension
section Specialization
variable {K σ:Type} [zrb K]
private def DJ (w:z3y σ K) :
  z3y (Option σ) K →ₐ[K] z3y σ K :=
 aeval (fun i=>i.elim w z9v)
private theorem duN (w:z3y σ K) (d:Option σ →₀ ℕ) (r :K) :
   DJ w (monomial d r)=w^(d none)*monomial d.some r := by
 rw [DJ,aeval_monomial,algebraMap_eq,Finsupp.prod_option_index]
 · rw [monomial_eq (s :=d.some) (a :=r)]
   simp only [Option.elim_none,Option.elim_some]
   ac_rfl
 · simp
 · intros
   rw [pow_add]
private theorem duM {q:z3y (Option σ) K} {n:ℕ}
    (hq:q.IsHomogeneous n) :
    (DJ 1 q).totalDegree≤n∧DJ 0 q=homogeneousComponent n (DJ 1 q) := by
  change q.IsWeightedHomogeneous (fun _=>1) n at hq
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero=>simp
  | add p q _ _ hp hq =>
    simp only [map_add]
    exact ⟨(totalDegree_add _ _).trans (max_le hp.1 hq.1),by rw [hp.2,hq.2]⟩
  | monomial d r hd =>
    rw [← zKx] at hd
    have hdeg:d none+d.some.degree=n:= by
      have hsplit :d.degree=d none+d.some.degree := by
        simp only [zqc]
        exact Finsupp.sum_option_index d (fun _ m=>m) (by simp) (by intros; rfl)
      rwa [← hsplit]
    simp only [duN,one_pow,one_mul]
    have hle :d.some.degree≤n:= by omega
    refine ⟨(totalDegree_monomial_le d.some r).trans hle,?_⟩
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial (d:=d.some) r rfl)]
    by_cases hz :d none=0
    · have he :n=d.some.degree := by omega
      simp [hz,he]
    · have he :n≠d.some.degree := by omega
      simp [zero_pow hz,he]
private theorem d2N {α B:Type} [za6 B] [zZE K B]
   (x :α→B) (t:B) {q:z3y α K} {n:ℕ} (hq:q.IsHomogeneous n) :
   aeval (fun i=>t*x i) q=t^n*aeval x q:= by
 change q.IsWeightedHomogeneous (fun _=>1) n at hq
 induction hq using IsWeightedHomogeneous.induction_on with
 | zero=>simp
 | add p q _ _ hp hq=>simp only [map_add,mul_add,hp,hq]
 | monomial d r hd =>
   rw [← zKx] at hd
   rw [← hd,aeval_monomial,aeval_monomial]
   simp only [zsa,mul_pow,zeY,zX0,
     zqc]
   ac_rfl
private theorem dLS (I:znc (z3y σ K))
  {q:z3y (Option σ) K} {n:ℕ} (hq:q.IsHomogeneous n) :
  TS I q=zdM n (zVv I (DJ 1 q)) := by
 let m:z3y σ K →ₐ[K] zM1 (z3y σ K ⧸ I) :=
  Polynomial.CAlgHom.comp (zvR K I)
 let x :Option σ→zM1 (z3y σ K ⧸ I) := fun i=>m (i.elim 1 z9v)
 have hscaled:TS I=aeval (fun i=>z7y*x i) := by
  apply zpH
  intro i
  cases i <;> simp [TS,x,m]
 have hx :aeval x=m.comp (DJ 1) := by
  apply zpH
  intro i
  simp only [aeval_X,zip,x,DJ]
 rw [hscaled,d2N x z7y hq,hx,zip]
 change z7y ^n*z1z (zVv I (DJ 1 q))= _
 exact (zxl (zVv I (DJ 1 q)) n).trans
  zoT
private theorem dLY (I J:znc (z3y σ K))
    (hcomponent : ∀ (f :z3y σ K) (n:ℕ),f∈I→f.totalDegree≤n →
      homogeneousComponent n f∈J) :
    ∃ s :Closure I →ₐ[K] (z3y σ K ⧸ J),
      zpX s∧s (Zu I)=0 ∧
      ∀ f,s (auA I f)=zVv J f := by
  let e :=(zvR K J).comp (DJ 0)
  have hker (q:z3y (Option σ) K) (hq:q∈JA I) :e q=0:= by
    change TS I q=0 at hq
    have h:TS I q =
        ∑ j∈z4x (q.totalDegree+1),
          zdM j (zVv I (DJ 1 (homogeneousComponent j q))) := by
      conv_lhs=>rw [← sum_homogeneousComponent q,map_sum]
      exact zUo rfl fun j _ =>
        dLS I (homogeneousComponent_isHomogeneous j q)
    have hm (n:ℕ) (hn:n∈z4x (q.totalDegree+1)) :
        DJ 0 (homogeneousComponent n q)∈J:= by
      have hcoeff :=congrArg (fun p:zM1 (z3y σ K ⧸ I)=>p.coeff n) h.symm
      have hz :zVv I (DJ 1 (homogeneousComponent n q))=0:= by
        simpa only [hq,zO6,zaW,
          zQm,Finset.sum_ite_eq',ite_eq_left hn] using hcoeff
      obtain ⟨hdeg,he⟩:=duM (homogeneousComponent_isHomogeneous n q)
      rw [he]
      exact hcomponent _ _ (Ideal.Quotient.eq_zero_iff_mem.mp hz) hdeg
    change zVv J (DJ 0 q)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← sum_homogeneousComponent q,map_sum]
    exact Ideal.sum_mem _ hm
  let s :=zTA (JA I) e hker
  have hLift (f :z3y σ K) :s (auA I f)=zVv J f := by
    have hid : (DJ (0:z3y σ K)).comp (rename some)=zhD K _:= by
      apply zpH
      intro i
      simp [DJ]
    change zVv J (DJ 0 (rename some f))=zVv J f
    exact congrArg (zVv J) (zmU hid f)
  refine ⟨s,?_,?_,hLift⟩
  · intro z
    obtain ⟨f,rfl⟩:=zld z
    exact ⟨auA I f,hLift f⟩
  · change zVv J (DJ 0 (z9v none))=0
    simp [DJ]
end Specialization
private theorem aDK {k σ:Type} [zrb k] [z85 σ] (c:σ→k) :
   (∑ i:σ,C (c i)*z9v i).IsHomogeneous 1 :=
 (homogeneousSubmodule σ k 1).sum_mem fun i _=>isHomogeneous_C_mul_X _ i
private theorem ccX {f :nW} {n:ℕ} (hf :f.IsHomogeneous n) :
  (tO f).IsHomogeneous n:= by
 have h (j:Fin 3) : (KT PV j.val).IsHomogeneous 1 := by
  exact aDK fun i:rS =>
    (i.val.choose j.val :dF)*PV^(i.val - j.val)
 simpa only [tO,one_mul] using hf.aeval _ h
private theorem ePs (g:nW) :
   (tO g).totalDegree≤g.totalDegree ∧
     homogeneousComponent g.totalDegree (tO g)=tO (aAz g) := by
 have hsum:tO g = ∑ j∈z4x (g.totalDegree+1),
     tO (homogeneousComponent j g) := by
   conv_lhs=>rw [← sum_homogeneousComponent g,map_sum]
 have hhom (j:ℕ) : (tO (homogeneousComponent j g)).IsHomogeneous j :=
   ccX (homogeneousComponent_isHomogeneous j g)
 constructor
 · rw [hsum]
   exact totalDegree_finsetSum_le fun j hj =>
     (hhom j).totalDegree_le.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
 · rw [hsum,map_sum]
   simp only [homogeneousComponent_of_mem (hhom _),Finset.sum_ite_eq,Finset.mem_range,
     Nat.lt_succ_self,ite_true,aAz]
theorem proof :axd.c2 := by
 intro P g d h
 have hg:tO g∈oV P:= by
   change g∈(oV P).comap tO
   rw [h.image]
   exact zCn (zT1 g)
 obtain ⟨hdeg,htop⟩:=ePs g
 have hc (f :mK) (n:ℕ) (hf :f∈oV P) (hn:f.totalDegree≤n) :
     homogeneousComponent n f∈oV (adN P) :=
   dOz P hf hn
 refine ⟨?_,dLY _ _ hc⟩
 change tO (aAz g)∈oV (adN P)
 rw [← htop]
 exact hc _ _ hg hdeg
end
end cx7
end
section
namespace bzv
noncomputable section
open MvPolynomial B7 Ey Pw
open scoped Polynomial
set_option maxHeartbeats 1000000
theorem bqW {F B σ:Type} [zrb F] [za6 B] [zZE F B]
  {p:z3y σ F} {n:ℕ} (hp:p.IsHomogeneous n) (x :σ→B) (s :B) :
  aeval (fun i=>s*x i) p=s^n*aeval x p:= by
 classical
 rw [← p.support_sum_monomial_coeff,map_sum,map_sum,zxw]
 apply zUo rfl
 intro m hm
 have hd:=hp.degree_eq_sum_deg_support hm
 simp only [aeval_monomial,zsa,mul_pow,zeY,
  zX0]
 rw [← hd]
 ac_rfl
def nY {F B σ:Type} [zrb F] [za6 B] [zZE F B] (d:σ→B) :
    z3y σ F →ₐ[F] B[X] :=
  aeval (fun i=>z1z (d i)*z7y)
theorem bNn {F B σ:Type} [zrb F] [za6 B] [zZE F B]
  (d:σ→B) {p:z3y σ F} {n:ℕ} (hp:p.IsHomogeneous n) :
  nY d p=zdM n (aeval d p) := by
 let c:B →ₐ[F] B[X] :=z97
 change aeval (fun i=>c (d i)*z7y) p= _
 simp_rw [mul_comm (c _),bqW hp]
 rw [← comp_aeval_apply d c p]
 change z7y ^n*z1z (aeval d p)= _
 rw [zxl,zoT]
private theorem gmm {F B σ:Type} [zrb F] [za6 B] [zZE F B]
   (d:σ→B) (p:z3y σ F) (n:ℕ) :
   (nY d p).coeff n=aeval d (homogeneousComponent n p) := by
 classical
 by_cases hn:n≤p.totalDegree
 · conv_lhs=>rw [← sum_homogeneousComponent p]
   rw [map_sum,zaW,zi6 n]
   · rw [bNn d (homogeneousComponent_isHomogeneous _ _)]
     simp
   · intro b _ hb
     rw [bNn d (homogeneousComponent_isHomogeneous _ _)]
     simp [zQm,hb]
   · simp [Finset.mem_range,hn]
 · rw [homogeneousComponent_eq_zero _ _ (by omega),map_zero]
   conv_lhs=>rw [← sum_homogeneousComponent p]
   rw [map_sum,Polynomial.finsetSum_coeff]
   refine Finset.sum_eq_zero fun b hb => ?_
   rw [bNn d (homogeneousComponent_isHomogeneous _ _)]
   have hbn:b≠n:= by simp only [Finset.mem_range] at hb; omega
   simp [Polynomial.coeff_monomial,hbn]
theorem c79 {F B:Type} [zrb F] [za6 B] [ztn B]
   [zZE F B] {m:ℕ} (d:Fin (m+1)→B) (hd:d 0≠0)
   (h : ¬ zq4 (nY (F:=F) d)) :
   ∃ p:z3y (Fin (m+1)) F,∃ n:ℕ,
     p.IsHomogeneous n∧aeval d p=0∧(finSuccEquiv F m p).coeff 0≠0:= by
 classical
 rw [injective_iff_map_eq_zero] at h
 push Not at h
 obtain ⟨p,hp,hp0⟩:=h
 let e :=finSuccEquiv F m
 let k :=(e p).natTrailingDegree
 have hdv :z7y ^k∣e p :=
   Polynomial.X_pow_dvd_iff.mpr fun j hj =>
     Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
 obtain ⟨r,hr⟩:=hdv
 let q:=e.symm r
 have hqeq :p=z9v 0^k*q:= by
   apply e.injective
   simpa [e,q,finSuccEquiv_X_zero] using hr
 have hq:nY d q=0:= by
   rw [hqeq,map_mul,map_pow] at hp
   refine (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ ?_)
   simpa [nY] using hd
 have hr0:r.coeff 0≠0:= by
   have hcoeff : (e p).coeff k=r.coeff 0:= by
     rw [hr]
     simpa using zxk r k 0
   rw [← hcoeff,Polynomial.coeff_natTrailingDegree_ne_zero]
   simpa [map_eq_zero_iff _ e.injective] using hp0
 obtain ⟨a,ha⟩:=exists_coeff_ne_zero hr0
 have haq: ((finSuccEquiv F m q).coeff 0).coeff a≠0:= by
   simpa [q,e] using ha
 rw [finSuccEquiv_coeff_coeff] at haq
 let n:=(a.cons 0).degree
 refine ⟨homogeneousComponent n q,n,homogeneousComponent_isHomogeneous _ _,?_,?_⟩
 · simpa [gmm] using congrArg (fun f :B[X]=>f.coeff n) hq
 · intro hz
   have hz' := congrArg (fun f :z3y (Fin m) F=>f.coeff a) hz
   rw [finSuccEquiv_coeff_coeff,coeff_homogeneousComponent,ite_eq_left rfl] at hz'
   exact haq (by simpa using hz')
private theorem enC {F:Type} [zrb F]
  {I:znc (z3y (Fin 3) F)}
  (g:z3y (Fin 2) F →ₐ[F] z3y (Fin 3) F ⧸ I)
  (hg:g.Finite) :I ≠ ⊥ := by
 intro hbot
 let e :=AlgEquiv.quotientBot F (z3y (Fin 2) F)
 have hdeg:=natDegree_affineHilbertPolynomial_le_of_finite (g.comp e.toAlgHom)
  (zfr hg e.toRingEquiv.finite)
 rw [hbot,natDegree_affineHilbertPolynomial_bot,natDegree_affineHilbertPolynomial_bot,
  zJa,zJa] at hdeg
 omega
theorem dOS {A:Type} [za6 A] [ztn A] [zZE dF A]
  (d:Fin 3→A) (L:Fin 2→nW) (hL:agE L (adu d)) :
  ¬ zq4 (nY (F:=dF) d) := by
 intro hinj
 apply enC (afO L (adu d)) hL.2
 exact (zli (ab4 d).toRingHom).mp hinj
theorem bXf {F:Type} [zrb F] [Infinite F]
   {p:z3y (Fin 3) F} {n:ℕ} (hp:p.IsHomogeneous n)
   (h0: (finSuccEquiv F 2 p).coeff 0≠0) : ∃ t:F,eval ![0,t,1] p≠0:= by
 classical
 by_contra! ht
 apply h0
 let s :Fin 2→Set F := ![Set.univ,{0}ᶜ]
 have hs : ∀ i,(s i).Infinite := by
   intro i
   fin_cases i
   · exact Set.infinite_univ
   · exact (Set.finite_singleton (0:F)).infinite_compl
 apply MvPolynomial.funext_set s hs
 intro x hx
 have hx1 :x 1≠0:= by
   simpa [s] using hx (1 :Fin 2) (Set.mem_univ _)
 have he : (fun i=>x 1*(![0,x 0/x 1,1] :Fin 3→F) i)=z4W 0 x := by
   ext i
   fin_cases i
   · simp
   · change x 1*(x 0/x 1)=z4W (α:= fun _=>F) 0 x (0:Fin 2).succ
     simp [div_eq_mul_inv,← mul_assoc,mul_comm (x 1) (x 0),hx1]
   · change x 1*1=z4W (α:= fun _=>F) 0 x (1 :Fin 2).succ
     rw [zVG,mul_one]
 have h:=bqW hp (![0,x 0/x 1,1] :Fin 3→F) (x 1)
 rw [he,aeval_eq_eval,aeval_eq_eval,ht,mul_zero] at h
 rw [eval_eq_eval_mv_eval',← zTt,z0b] at h
 simpa using h
end
end bzv
end
section
namespace cx0
noncomputable section
open MvPolynomial
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ:Type} [zrb k]
private abbrev bY (I:znc (z3y σ k)) (i:σ) :
   znc (z3y σ k) :=
 I ⊔ zye {z9v i - 1}
private def dO (I:znc (z3y σ k)) (n:ℕ) :
   Submodule k (z3y σ k ⧸ I) :=
 (homogeneousSubmodule σ k n).map (zvR k I).toLinearMap
private theorem azB {I:znc (z3y σ k)} {n:ℕ}
  {z :z3y σ k ⧸ I} :
  z∈dO I n ↔ ∃ p:z3y σ k,p.IsHomogeneous n ∧
    zVv I p=z :=
 Submodule.mem_map
private instance [Finite σ] (I:znc (z3y σ k)) (n:ℕ) :
  zAa k (dO I n) :=
 Module.Finite.of_fg ((homogeneousSubmodule_fg σ k n).map _)
private theorem eLc (I:znc (z3y σ k)) (n:ℕ) :
  dO I n≤quotientDegreeLE I n:= by
 intro z hz
 obtain ⟨p,hp,rfl⟩:=azB.mp hz
 exact mk_mem_quotientDegreeLE hp.totalDegree_le
private theorem ctP {p:z3y σ k} {n:ℕ}
  (hp:p.totalDegree≤n+1) :
  (p - homogeneousComponent (n+1) p).totalDegree≤n:= by
 classical
 apply Finset.sup_le
 intro d hd
 change d.degree≤n
 rw [zuk,coeff_sub,coeff_homogeneousComponent] at hd
 have hne :d.degree≠n+1 := by
  intro he
  simp [he] at hd
 simp only [ite_eq_right hne,sub_zero] at hd
 exact zeh (lt_of_le_of_ne
  ((le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)).trans hp) hne)
private theorem eLb [Finite σ] {I:znc (z3y σ k)}
   (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) (n:ℕ) :
   zsE k (dO I (n+1))+affineHilbertFunction I n =
     affineHilbertFunction I (n+1) := by
 have hsup:quotientDegreeLE I n ⊔ dO I (n+1)=quotientDegreeLE I (n+1) := by
   refine le_antisymm (sup_le (quotientDegreeLE_mono I (zqk n))
     (eLc I (n+1))) ?_
   intro z hz
   obtain ⟨p,hp,rfl⟩:=mem_quotientDegreeLE.mp hz
   refine Submodule.mem_sup.mpr ⟨_,mk_mem_quotientDegreeLE
     (ctP hp),zVv I (homogeneousComponent (n+1) p),
     azB.mpr ⟨_,homogeneousComponent_isHomogeneous (n+1) p,rfl⟩,?_⟩
   rw [← map_add,sub_add_cancel]
 have hinf :quotientDegreeLE I n ⊓ dO I (n+1) = ⊥ := by
   apply (Submodule.eq_bot_iff _).mpr
   intro z hz
   obtain ⟨a,ha,haz⟩:=mem_quotientDegreeLE.mp hz.1
   obtain ⟨b,hb,hbz⟩:=azB.mp hz.2
   have hba :b-a∈I:=Ideal.Quotient.eq.mp (hbz.trans haz.symm)
   have hm:=homogeneousComponent_mem_of_mem hI hba (n+1)
   rw [map_sub,homogeneousComponent_eq_self hb,
     homogeneousComponent_eq_zero _ _ (zB1 ha),sub_zero] at hm
   rw [← hbz,z1Q]
   exact hm
 have h:=Submodule.finrank_sup_add_finrank_inf_eq (quotientDegreeLE I n) (dO I (n+1))
 rw [hsup,hinf,finrank_bot,add_zero] at h
 exact (add_comm _ _).trans h.symm
private theorem cHw (i:σ) (p:z3y σ k) (m:ℕ) :
  homogeneousComponent m (p*z9v i) =
   if 1≤ m then homogeneousComponent (m - 1) p*z9v i else 0:= by
 simpa only [← DirectSum.Decomposition.decompose'_eq,MvPolynomial.decomposition.decompose'_apply]
  using DirectSum.coe_decompose_mul_of_right_mem
   (homogeneousSubmodule σ k) m (a :=p) (isHomogeneous_X k i)
private def bsO (I:znc (z3y σ k)) (i:σ) (n:ℕ) :
   dO I n →ₗ[k] dO I (n+1) :=
 ((zzN k (zVv I (z9v i))).domRestrict _).codRestrict _
   fun z=> by
    obtain ⟨p,hp,hpz⟩:=azB.mp z.property
    change zVv I (z9v i)*z.val∈dO I (n+1)
    rw [← hpz,← map_mul,mul_comm]
    exact azB.mpr ⟨_,hp.mul (isHomogeneous_X k i),rfl⟩
private theorem c0V (I:znc (z3y σ k)) (i:σ) {n:ℕ}
   {p:z3y σ k} (hp:p.IsHomogeneous n) :
   (bsO I i n ⟨zVv I p,azB.mpr ⟨p,hp,rfl⟩⟩).val =
     zVv I (p*z9v i) := by
 change zVv I (z9v i)* zVv I p= _
 rw [mul_comm,map_mul]
private theorem eD9 [Finite σ] {I:znc (z3y σ k)}
   (i:σ) (hI:I.IsHomogeneous (homogeneousSubmodule σ k))
   (hrad : ∀ j:σ,z9v j∈(I ⊔ zye {z9v i}).radical) :
   ∃ N :ℕ,∀ n≥N,zpX (bsO I i n) := by
 let J:znc (z3y σ k) :=I ⊔ zye {z9v i}
 have hvars :idealOfVars σ k≤J.radical:= by
   apply Ideal.span_le.mpr
   rintro _ ⟨j,rfl⟩
   exact hrad j
 obtain ⟨N,hN⟩:=Ideal.exists_pow_le_of_le_radical_of_fg hvars (idealOfVars_fg σ k)
 refine ⟨N,fun n hn z => ?_⟩
 obtain ⟨p,hp,hpz⟩:=azB.mp z.property
 have hpJ:p∈J:=hN ((mem_pow_idealOfVars_iff N p).mpr fun d hd=> by
   have he :d.degree=n+1 := by
     by_contra hne
     exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero hne)
   omega)
 obtain ⟨a,ha,b,hb,he⟩:=Submodule.mem_sup.mp hpJ
 obtain ⟨q,rfl⟩:=Ideal.mem_span_singleton'.mp hb
 have hc:=congrArg (homogeneousComponent (n+1)) he
 rw [map_add,cHw,ite_eq_left (by omega),Nat.add_sub_cancel,
   homogeneousComponent_eq_self hp] at hc
 refine ⟨⟨_,azB.mpr ⟨_,homogeneousComponent_isHomogeneous n q,rfl⟩⟩,
   Subtype.ext ?_⟩
 rw [c0V I i (homogeneousComponent_isHomogeneous n q),← hpz,← hc,map_add,
   Ideal.Quotient.eq_zero_iff_mem.mpr (homogeneousComponent_mem_of_mem hI ha _),zero_add]
private theorem d3x [Finite σ] {I:znc (z3y σ k)}
   (hI:I.IsHomogeneous (homogeneousSubmodule σ k))
   (hd: (affineHilbertPolynomial I).natDegree=1) :
   ∃ N :ℕ,∀ n≥N,
     (zsE k (dO I (n+1)) :ℚ)=(affineHilbertPolynomial I).leadingCoeff := by
 obtain ⟨N,hN⟩:=exists_eval_affineHilbertPolynomial I
 refine ⟨N,fun n hn => ?_⟩
 let P:=affineHilbertPolynomial I
 have hdeg: (zW9 1 P).natDegree=0 :=
   za7 (by simpa [P,hd] using Polynomial.natDegree_backwardDifference_le 1 P)
 have hcoeff :=Polynomial.coeff_backwardDifference_natDegree_sub_one (1 :ℚ) P
 change (zW9 1 P).coeff (P.natDegree - 1)= _ at hcoeff
 have hP:P.natDegree=1 :=hd
 simp only [hP,Nat.sub_self,z4o,mul_one,one_mul] at hcoeff
 have hback :zW9 1 P=z1z P.leadingCoeff :=
   (Polynomial.eq_C_of_natDegree_eq_zero hdeg).trans (congrArg z1z hcoeff)
 have hev :=congrArg (fun f :ℚ[X]=>f.eval ((n+1 :ℕ) :ℚ)) hback
 change (zW9 1 P).eval ((n+1 :ℕ) :ℚ)= _ at hev
 have hncast: ((n+1 :ℕ) :ℚ) - 1=(n:ℚ) := by simp
 rw [Polynomial.eval_backwardDifference,zFf,hncast] at hev
 change (affineHilbertPolynomial I).eval ((n+1 :ℕ) :ℚ) -
   (affineHilbertPolynomial I).eval (n:ℚ)= _ at hev
 rw [hN (n+1) (hn.trans (zqk n)),hN n hn] at hev
 have hs : (zsE k (dO I (n+1)) :ℚ) +
     (affineHilbertFunction I n:ℚ)=(affineHilbertFunction I (n+1) :ℚ) := by
   exact_mod_cast eLb hI n
 linarith only [hs,hev]
private theorem enk {I:znc (z3y σ k)} (i:σ)
    (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) {n:ℕ}
    (hcancel : ∀ m≥n,∀ {q:z3y σ k},q.IsHomogeneous m →
      q*z9v i∈I→q∈I)
    {p:z3y σ k} (hp:p.IsHomogeneous n) (hpJ:p∈bY I i) :p∈I:= by
  obtain ⟨a,ha,b,hb,he⟩:=Submodule.mem_sup.mp hpJ
  obtain ⟨f,rfl⟩:=Ideal.mem_span_singleton'.mp hb
  let t (m:ℕ) :=homogeneousComponent m f
  have hrel (m:ℕ) :homogeneousComponent m p -
      ((if 1≤ m then t (m - 1)*z9v i else 0) - t m)∈I:= by
    have hc:=congrArg (homogeneousComponent m) he
    rw [map_add,mul_sub,mul_one,map_sub,cHw] at hc
    dsimp only [t]
    rw [← hc,add_sub_cancel_right]
    exact homogeneousComponent_mem_of_mem hI ha m
  have hsucc (m:ℕ) :homogeneousComponent (m+1) p -
      (t m*z9v i - t (m+1))∈I:= by
    simpa only [ite_eq_left (show 1≤ m+1 by omega),Nat.add_sub_cancel] using hrel (m+1)
  have hhigh:t n∈I:= by
    let M:=max n (f.totalDegree+1)
    refine Nat.decreasingInduction' (P:= fun m=>t m∈I) (n:=M) (m:=n)
      (fun m _ hm ih => ?_) (le_max_left _ _) ?_
    · have ht:=hsucc m
      rw [homogeneousComponent_eq_zero _ _ (hp.totalDegree_le.trans_lt (by omega)),
        zero_sub,neg_mem_iff] at ht
      exact hcancel m hm (homogeneousComponent_isHomogeneous m f)
        ((zSM I ih).mp ht)
    · dsimp only [t]
      rw [homogeneousComponent_eq_zero _ _ (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))]
      exact I.zero_mem
  have hlow (m:ℕ) :m<n→t m∈I:= by
    induction m with
    | zero =>
      intro hm
      have ht:=hrel 0
      rw [homogeneousComponent_of_mem hp,ite_eq_right (by omega :0≠n),
        ite_eq_right (by omega : ¬ 1≤0)] at ht
      simpa only [zero_sub,neg_neg] using ht
    | succ m ih =>
      intro hm
      have ht:=hsucc m
      rw [homogeneousComponent_of_mem hp,ite_eq_right (Nat.ne_of_lt hm),zero_sub,neg_mem_iff] at ht
      exact (Submodule.sub_mem_iff_right I (I.mul_mem_right _ (ih (Nat.lt_of_succ_lt hm)))).mp ht
  have ht:=hrel n
  rw [homogeneousComponent_eq_self hp] at ht
  apply (zSM I ?_).mp ht
  apply I.sub_mem _ hhigh
  split_ifs with hn
  · exact I.mul_mem_right _ (hlow _ (by omega))
  · exact I.zero_mem
private theorem b54 (I:znc (z3y σ k)) (i:σ)
   {n:ℕ} {p:z3y σ k} (hp:p.totalDegree≤n) :
   ∃ q:z3y σ k,q.IsHomogeneous n ∧
     zVv (bY I i) q=zVv (bY I i) p:= by
 classical
 let J:=bY I i
 have hi:zVv J (z9v i)=1 := by
   apply sub_eq_zero.mp
   rw [← (zVv J).map_one,← map_sub,z1Q]
   exact zs0 (z5J _)
 refine ⟨∑ d∈z4x (p.totalDegree+1),
   z9v i^(n - d)*homogeneousComponent d p,IsHomogeneous.sum _ _ _ ?_,?_⟩
 · intro d hd
   have hdn:=(zeh (Finset.mem_range.mp hd)).trans hp
   simpa only [zxt hdn] using
     (isHomogeneous_X_pow (R:=k) i (n - d)).mul (homogeneousComponent_isHomogeneous d p)
 · change zVv J _=zVv J p
   rw [map_sum]
   simp only [map_mul,map_pow,hi,one_pow,one_mul]
   rw [← map_sum,sum_homogeneousComponent]
private theorem dIA [Finite σ] {I:znc (z3y σ k)} (i:σ)
   (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) {n:ℕ}
   (hcancel : ∀ m≥n,∀ {q:z3y σ k},q.IsHomogeneous m →
     q*z9v i∈I→q∈I) :
   affineHilbertFunction (bY I i) n=zsE k (dO I n) := by
 let J:=bY I i
 let q:=z5F k (show I≤J from le_sup_left)
 let cut:dO I n →ₗ[k] quotientDegreeLE J n :=
   (q.toLinearMap.domRestrict _).codRestrict _ fun z=> by
     obtain ⟨p,hp,hpz⟩:=azB.mp z.property
     change q z.val∈quotientDegreeLE J n
     rw [← hpz]
     exact mk_mem_quotientDegreeLE hp.totalDegree_le
 have hsurj:zpX cut:= by
   intro z
   obtain ⟨p,hp,hpz⟩:=mem_quotientDegreeLE.mp z.property
   obtain ⟨r,hr,hrp⟩:=b54 I i hp
   exact ⟨⟨zVv I r,azB.mpr ⟨r,hr,rfl⟩⟩,Subtype.ext (hrp.trans hpz)⟩
 have hinj:zq4 cut:= by
   rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
   intro z hz
   obtain ⟨p,hp,hpz⟩:=azB.mp z.property
   have hm:q z.val=0:=congrArg Subtype.val hz
   rw [← hpz] at hm
   have hpJ:p∈J:=Ideal.Quotient.eq_zero_iff_mem.mp hm
   apply Subtype.ext
   change z.val=0
   rw [← hpz,z1Q]
   exact enk i hI hcancel hp hpJ
 exact (LinearEquiv.ofBijective cut ⟨hinj,hsurj⟩).finrank_eq.symm
theorem proof :ap5.c3:= by
 intro k σ _ _ I i hI hd hrad
 obtain ⟨N,hN⟩:=eD9 i hI hrad
 obtain ⟨M,hM⟩:=d3x hI hd
 have hcancel (m:ℕ) (hm:max N (M+1)≤ m) {p:z3y σ k}
     (hp:p.IsHomogeneous m) (hpX:p*z9v i∈I) :p∈I:= by
   have hN' : N≤ m:=(le_max_left _ _).trans hm
   have hM' : M+1≤ m:=(le_max_right _ _).trans hm
   have he :m - 1+1=m:= by omega
   have hfin:zsE k (dO I m)=zsE k (dO I (m+1)) := by
     have hh:=hM (m - 1) (by omega)
     rw [he] at hh
     exact_mod_cast hh.trans (hM m (by omega)).symm
   have hi:zq4 (bsO I i m) :=
     (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr (hN m hN')
   let z :dO I m:=⟨zVv I p,azB.mpr ⟨p,hp,rfl⟩⟩
   have hz :bsO I i m z=0:=Subtype.ext (by
     change (bsO I i m z).val=0
     rw [c0V I i hp,z1Q]
     exact hpX)
   have hz' : z=0:=hi (hz.trans (map_zero _).symm)
   exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hz')
 change affineHilbertPolynomial (bY I i)=z1z (affineHilbertPolynomial I).leadingCoeff
 symm
 apply eq_affineHilbertPolynomial_of_eval_eq (N₀:=max N (M+1))
 intro n hn
 rw [zFf,dIA i hI (fun m hm=>hcancel m (hn.trans hm))]
 have hM' : M+1≤n:=(le_max_right _ _).trans hn
 have hh:=hM (n - 1) (by omega)
 rw [show n - 1+1=n by omega] at hh
 exact hh.symm
end
end cx0
end
section
namespace bzw
noncomputable section
open B7 Ey axd MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
private theorem c0L {R A:Type} [za6 R] [ztn R] [za6 A]
    (ρ:R →+* A) (z :A) (p:zM1 R) (hp:p.Monic) (hz :p.eval₂ ρ z=0)
    (hs :zpX (zqf ρ z)) :
    ρ.Finite ∧
      (letI:zeq R A:=zki A ρ
       z1x R A≤(p.natDegree :Cardinal)) := by
  let t:=AdjoinRoot.lift ρ z hz
  have ht:t.comp (AdjoinRoot.of p)=ρ:=AdjoinRoot.lift_comp_of hz
  have hts :zpX t:= by
    intro a
    obtain ⟨q,hq⟩:=hs a
    exact ⟨AdjoinRoot.mk p q,(AdjoinRoot.lift_mk hz q).trans hq⟩
  constructor
  · have hfinite : (AdjoinRoot.of p).Finite :=
      RingHom.finite_algebraMap.mpr hp.finite_adjoinRoot
    rw [← ht]
    exact (zO7 t hts).comp hfinite
  · letI:zeq R A:=zki A ρ
    let u:AdjoinRoot p →ₗ[R] A :=
      { toFun:=t
        map_add' := t.map_add
        map_smul' := fun r a=> by
          rw [zd5]
          change t (AdjoinRoot.of p r*a)=ρ r*t a
          rw [map_mul]
          exact congrArg (· * t a) (zmU ht r) }
    refine (LinearMap.rank_le_of_surjective u hts).trans ?_
    rw [← (AdjoinRoot.powerBasis' hp).basis.mk_eq_rank'']
    simp
private theorem dgr {F D σ:Type} [za6 F] [Semiring D]
   (I:znc (z3y σ F)) (s :D →+* (z3y σ F ⧸ I))
   (hc : ∀ c:F,∃ t,s t=zVv I (C c))
   (hx : ∀ i:σ,∃ t,s t=zVv I (z9v i)) :zpX s := by
 intro a
 obtain ⟨p,rfl⟩:=zld a
 induction p using z5i with
 | C c=>exact hc c
 | add p q hp hq =>
     obtain ⟨u,hu⟩:=hp
     obtain ⟨v,hv⟩:=hq
     exact ⟨u+v,by rw [map_add,hu,hv,map_add]⟩
 | mul_X p i hp =>
     obtain ⟨u,hu⟩:=hp
     obtain ⟨v,hv⟩:=hx i
     exact ⟨u*v,by rw [map_mul,hu,hv,map_mul]⟩
private theorem cNi {R A:Type} [CommSemiring R] [CommSemiring A]
   (ρ:R →+* A) (z :A) (a b:R) :
   zqf ρ z (z1z a+Polynomial.C b*z7y) =
     ρ a+ρ b*z := by
 change (z1z a+Polynomial.C b*z7y).eval₂ ρ z= _
 rw [Polynomial.eval₂_add,zxy,zJU,zJU,
   zC9]
private theorem bXf {F:Type} [zrb F] [Infinite F]
   (g:z3y (Fin 3) F) (hg:0<g.totalDegree) :
   ∃ v :Fin 3→F,v 0≠0∧eval v (homogeneousComponent g.totalDegree g)≠0:= by
 classical
 have hs :g.support.Nonempty := by
   rw [support_nonempty]
   rintro rfl
   simp at hg
 obtain ⟨d,hd,hdeg⟩ :=
   Finset.exists_mem_eq_sup g.support hs (fun d=>d.degree)
 have htop:homogeneousComponent g.totalDegree g≠0:= by
   intro h
   have hdeg' : d.degree=g.totalDegree :=hdeg.symm
   have hcoeff : (homogeneousComponent g.totalDegree g).coeff d≠0:= by
     simpa only [coeff_homogeneousComponent,ite_eq_left hdeg'] using mem_support_iff.mp hd
   exact hcoeff (by simp [h])
 have hprod:z9v 0*homogeneousComponent g.totalDegree g≠0 :=
   mul_ne_zero (X_ne_zero _) htop
 have hex : ∃ v,eval v (z9v 0*homogeneousComponent g.totalDegree g)≠0:= by
   by_contra! h
   apply hprod
   apply zjN
   intro v
   simpa only [map_zero] using h v
 obtain ⟨v,hv⟩:=hex
 rw [map_mul,eval_X] at hv
 exact ⟨v,left_ne_zero_of_mul hv,right_ne_zero_of_mul hv⟩
private def u7 (v :Fin 3→dF) (i:Fin 2) :nW :=
 z9v i.succ - C (v i.succ*(v 0)⁻¹)*z9v 0
private def direction (v :Fin 3→dF) :nW :=
 C ((v 0)⁻¹)*z9v 0
private def Wg:Fin 3→l5 :=
 z4W 0 z9v
private theorem coord (v :Fin 3→dF) (hv :v 0≠0) (i:Fin 3) :
   z9v i=aeval (u7 v) (Wg i)+C (v i)*direction v := by
 refine Fin.cases ?_ (fun j => ?_) i
 · simp only [Wg,zhe,map_zero,zero_add,direction,← mul_assoc,← map_mul,
    mul_inv_cancel₀ hv,map_one,one_mul]
 · simp only [Wg,zVG,aeval_X,u7,direction,← mul_assoc,← map_mul]
   abel
private theorem cH6 {A:Type} [za6 A] [zZE dF A]
    (v :Fin 3→dF) (hv :v 0≠0) (q:nW →ₐ[dF] A)
    (i:Fin 3) :
    q (z9v i) =
      aeval (fun j=>q (u7 v j)) (Wg i) +
        algebraMap dF A (v i)*q (direction v) := by
  have h:=congrArg q (coord v hv i)
  simpa only [map_add,map_mul,comp_aeval_apply,← algebraMap_eq,zKk] using h
private theorem gCi (g:nW) (v :Fin 3→dF) (h0:v 0≠0)
    (hv :eval v (aAz g)≠0) :
    agE (u7 v) (zye {aAz g}) := by
  let J:znc nW:=zye {aAz g}
  let A:=nW ⧸ J
  let q:nW →ₐ[dF] A:=zvR dF J
  let β:l5 →ₐ[dF] A:=aeval fun j=>q (u7 v j)
  let ρ:l5 →+* A:=β.toRingHom
  let f :=algebraMap dF l5
  let z :=q (direction v)
  have hcomp:ρ.comp f=algebraMap dF A:=β.comp_algebraMap
  have hcoord (i:Fin 3) :q (z9v i)=ρ (Wg i)+ρ (f (v i))*z := by
    have hh:=zmU hcomp (v i)
    change ρ (f (v i))=algebraMap dF A (v i) at hh
    rw [hh]
    exact cH6 (A:=A) v h0 q i
  let p:=aIE f g v Wg 0
  have hp:p.Monic:=(c0J f g v Wg 0 hv).1
  have hz :p.eval₂ ρ z=0:= by
    refine c0I f g v Wg 0 ρ z ?_
    simp only [← hcoord,hcomp,map_zero,enj]
    have heval :eval₂ (algebraMap dF A) (fun i=>q (z9v i)) (aAz g) =
        q (aAz g) := by
      rw [← aeval_def]
      exact zmU (by ext i; simp : (aeval fun i=>q (z9v i))=q) _
    change eval₂ (algebraMap dF A) (fun i=>q (z9v i)) (aAz g)=0
    rw [heval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (zCn (zT1 _))
  have hsurj:zpX (zqf ρ z) := by
    refine dgr (D:=zM1 l5) J (zqf ρ z) ?_ ?_
    · intro c
      refine ⟨z1z (f c),?_⟩
      rw [z4Q,zJU]
      exact (zmU hcomp c).trans (q.commutes c |>.symm)
    · intro i
      refine ⟨z1z (Wg i)+Polynomial.C (f (v i))*z7y,?_⟩
      exact (cNi (R:=l5) (A:=A) ρ z _ _).trans (hcoord i).symm
  refine ⟨fun i=>(isHomogeneous_X _ _).sub (isHomogeneous_C_mul_X _ _),?_⟩
  have hβ:afO (u7 v) J=β:= by
    ext i
    exact (congrArg q (aeval_X (u7 v) i)).trans
      (aeval_X (fun j=>q (u7 v j)) i).symm
  have heq : (afO (u7 v) J).toRingHom=ρ :=
    congrArg (fun b:l5 →ₐ[dF] A=>b.toRingHom) hβ
  change @RingHom.Finite l5 A _ _ (afO (u7 v) J).toRingHom
  rw [heq]
  exact (c0L (A:=A) ρ z p hp hz hsurj).1
private theorem dLW (g:nW) (v :Fin 3→dF) (h0:v 0≠0)
    (hv :eval v (aAz g)≠0) :
    a2z (u7 v) (zye {g})≤(g.totalDegree :Cardinal) := by
  let I:znc nW:=zye {g}
  let J:=JA I
  let A:=Closure I
  let q:nW →ₐ[dF] A :=
    (zvR dF J).comp (rename some)
  let β:l5 →ₐ[dF] A:=aeval fun i=>q (u7 v i)
  let ρ: (zM1 l5) →+* A:=afp (u7 v) I
  let f :=algebraMap dF (zM1 l5)
  let a := fun i=>z1z (Wg i)
  let w:zM1 l5:=z7y
  let z :=q (direction v)
  have hρC (r :l5) :ρ (z1z r)=β r :=
    zJU _ _
  have hρw:ρ w=Zu I:=zC9 _ _
  have hcomp:ρ.comp f=algebraMap dF A:= by
    ext c
    change ρ (z1z (algebraMap dF l5 c))= _
    rw [hρC,zKk]
  have hcoord (i:Fin 3) :q (z9v i)=ρ (a i)+ρ (f (v i))*z := by
    have hh:=zmU hcomp (v i)
    change ρ (f (v i))=algebraMap dF A (v i) at hh
    dsimp only [a]
    rw [hρC,hh]
    exact cH6 (A:=A) v h0 q i
  have hqX (i:Fin 3) :q (z9v i)=zVv J (z9v (some i)) := by
    change zVv J (rename some (z9v i))= _
    rw [rename_X]
  let p:=aIE f g v a w
  obtain ⟨hp,hdeg⟩:=c0J f g v a w hv
  have hz :p.eval₂ ρ z=0:= by
    refine c0I f g v a w ρ z ?_
    simp only [hcomp,← hcoord,hρw]
    letI:za6 (nW ⧸ I) :=Ideal.Quotient.commRing I
    letI:za6 (zM1 (nW ⧸ I)) :=Polynomial.commRing
    let k :=(TS I).toRingHom
    let eqn:=aDn znf g (fun i=>z9v (some i))
      (z9v none)
    have heqn:zVv J eqn =
        aDn (algebraMap dF A) g (fun i=>q (z9v i)) (Zu I) := by
      have hx : (zVv J ∘ fun i=>z9v (some i)) =
          fun i=>q (z9v i) :=funext fun i=>(hqX i).symm
      dsimp only [eqn]
      rw [b8D,hx]
      rfl
    rw [← heqn]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change k eqn=0
    dsimp only [eqn]
    rw [b8D (R:=z3y (Option (Fin 3)) dF)
      (S:=zM1 (nW ⧸ I)) k]
    let m:nW →+* (nW ⧸ I) :=zVv I
    have hkcomp:k.comp znf=Polynomial.C.comp (m.comp znf) := by
      refine zz4 fun c => ?_
      change (TS I) (C c)=z1z (m (C c))
      exact aeval_C _ c
    have hkx : (k ∘ fun i:Fin 3=>z9v (some i)) =
        fun i=>z1z (m (z9v i))*Polynomial.X:= by
      funext i
      change (TS I) (z9v (some i))= _
      exact aeval_X _ (some i)
    have hkw:k (z9v none)=Polynomial.X:=aeval_X _ none
    simp only [hkcomp,hkx,hkw]
    rw [enh (R:=zM1 (nW ⧸ I))]
    have hm:eval₂ (Polynomial.C.comp (m.comp znf))
        (fun i=>z1z (m (z9v i))) g=z1z (m g) := by
      have he :eval₂Hom (Polynomial.C.comp (m.comp znf))
          (fun i=>z1z (m (z9v i)))=Polynomial.C.comp m:= by
        apply zXT <;> simp
      exact zmU he g
    have hm0:m g=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (zCn (zT1 _))
    rw [hm,hm0,map_zero,zero_mul]
  have hsurj:zpX (zqf ρ z) := by
    refine dgr (D:=zM1 (zM1 l5)) J
      (zqf ρ z) ?_ ?_
    · intro c
      refine ⟨z1z (f c),?_⟩
      rw [z4Q,zJU]
      exact zmU hcomp c
    · intro i
      cases i with
      | none=>exact ⟨Polynomial.C w,(Polynomial.eval₂_C _ _).trans hρw⟩
      | some i =>
          refine ⟨z1z (a i)+Polynomial.C (f (v i))*z7y,?_⟩
          rw [← hqX]
          exact (cNi (R:=zM1 l5) (A:=A) ρ z _ _).trans (hcoord i).symm
  unfold a2z
  rw [← hdeg]
  exact (c0L (A:=A) ρ z p hp hz hsurj).2
theorem proof :axd.c1 := by
 intro g hg
 letI:Infinite dF:=Infinite.of_injective _
  (zxb (zM1 aR.ao) dF)
 obtain ⟨v,h0,hv⟩:=bXf g hg
 exact ⟨u7 v,gCi g v h0 hv,dLW g v h0 hv⟩
end
end bzw
end
section
namespace cyx
open aR dN rW MvPolynomial
theorem proof :NS.c1 := by
 intro A
 letI:zZE ao GeoField:=ni.toAlgebra
 change affineHilbertPolynomial (A.map (zDK (algebraMap ao GeoField))) =
  affineHilbertPolynomial A
 exact Ey.ZI (E :=GeoField) A
end cyx
end
section
namespace ban
noncomputable section
open B7 Pw MvPolynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
private theorem gwy {k σ:Type} [zrb k] (u:σ →₀ k) :
  (sumSMulX u).IsHomogeneous 1 := by
 classical
 rw [sumSMulX,z0S,Finsupp.sum]
 exact (homogeneousSubmodule σ k 1).sum_mem (fun i _ =>
  (homogeneousSubmodule σ k 1).smul_mem _ (isHomogeneous_X _ i))
private theorem gwz {k σ:Type} [zrb k]
   {p:z3y σ k} (hp:p.IsHomogeneous 1) :
   ∃ u:σ →₀ k,sumSMulX u=p:= by
 classical
 let I:=p.support
 have hx (v :σ →₀ ℕ) (h:v.degree=1) : ∃ i:σ,zhf i 1=v :=
   show v∈zxp (fun i:σ=>zhf i 1) from Finsupp.range_single_one ▸ h
 let u:σ →₀ k := ∑ v∈I,if h:v.degree=1 then
     zhf ((hx v h).choose) (p.coeff v) else 0
 refine ⟨u,?_⟩
 rw [show p = ∑ v∈I,monomial v (p.coeff v) from p.as_sum]
 simp only [u,map_sum]
 refine zUo rfl fun v hv => ?_
 have hd:v.degree=1 := by
   rw [zKx]
   exact hp (mem_support_iff.mp hv)
 simp only [dite_eq_left hd,sumSMulX,Finsupp.linearCombination_single]
 rw [zd5,algebraMap_eq]
 change C (p.coeff v)*z9v _=monomial v (p.coeff v)
 rw [C_mul_X_eq_monomial]
 exact congrArg (fun m=>monomial m (p.coeff v)) (hx v hd).choose_spec
private theorem bT1 {k σ τ:Type} [zrb k]
  (y :σ→z3y τ k) (u:σ →₀ k) :
  aeval y (sumSMulX u)=zzF k y u:= by
 simp [sumSMulX,z0S,Finsupp.sum]
private def ew2 {k σ:Type} [zrb k]
   (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) :z3y σ k ≃ₐ[k] z3y σ k := by
 let form (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) (i:σ) :=sumSMulX (e (zhf i 1))
 have hform (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) (u:σ →₀ k) :
     aeval (form e) (sumSMulX u)=sumSMulX (e u) := by
   rw [bT1]
   have hmap :zzF k (form e)=sumSMulX.comp e.toLinearMap:= by
     apply (zXB :z39 σ k (σ →₀ k)).ext
     intro i
     simp [form,zwk]
   rw [hmap]
   rfl
 have hcomp (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) :
     (aeval (form e)).comp (aeval (form e.symm))=zhD k (z3y σ k) := by
   apply algHom_ext
   intro i
   simp only [zip,aeval_X,AlgHom.id_apply]
   change aeval (form e) (sumSMulX (e.symm (zhf i 1)))=z9v i
   rw [hform,LinearEquiv.apply_symm_apply]
   simp [sumSMulX]
 exact AlgEquiv.ofAlgHom (aeval (form e)) (aeval (form e.symm)) (hcomp e) (hcomp e.symm)
theorem d4o {k :Type} [zrb k] (L:Fin 2→z3y (Fin 3) k)
    (hL : ∀ i,(L i).IsHomogeneous 1) (hi:zq4 (aeval L:z3y (Fin 2) k →ₐ[k] z3y (Fin 3) k)) :
    ∃ e :z3y (Fin 3) k ≃ₐ[k] z3y (Fin 3) k,
      (∀ i:Fin 2,e (z9v i.succ)=L i) ∧
      (∀ i,(e (z9v i)).IsHomogeneous 1) := by
  classical
  choose u hu using fun i=>gwz (hL i)
  have hli:z14 k u:= by
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    intro a b hab
    have hh:aeval L (sumSMulX a)=aeval L (sumSMulX b) := by
      rw [bT1,bT1]
      have hcomp:zzF k L =
          sumSMulX.comp (zzF k u) := by
        apply (zXB :z39 (Fin 2) k (Fin 2 →₀ k)).ext
        intro i
        simp [zwk,hu]
      simp only [hcomp,LinearMap.comp_apply,hab]
    ext i
    simpa only [coeff_sumSMulX] using congrArg (fun p:z3y (Fin 2) k=>p.coeff (zhf i 1)) (hi hh)
  let V:=Fin 3 →₀ k
  let D:z39 (Fin 3) k V:=zXB
  have hdim:zsE k V=3:= by
    simpa using Module.finrank_eq_card_basis D
  have hproper :Submodule.span k (zxp u) ≠ ⊤ := by
    intro h
    have hspan:=finrank_span_eq_card hli
    rw [h,finrank_top,hdim,zgY] at hspan
    omega
  obtain ⟨v,hv⟩ : ∃ v :V,v∉Submodule.span k (zxp u) := by
    by_contra! h
    exact hproper (eq_top_iff.mpr fun x _=>h x)
  let B:=basisOfLinearIndependentOfCardEqFinrank (linearIndependent_finCons.mpr ⟨hli,hv⟩)
    (show Fintype.card (Fin 3)=zsE k V by simp [hdim])
  let e :=D.equiv B (Equiv.refl _)
  refine ⟨ew2 e,?_,?_⟩
  · intro i
    change (aeval (fun j=>sumSMulX (e (zhf j 1)))) (z9v i.succ)=L i
    rw [aeval_X,show zhf i.succ 1=D i.succ from rfl,Module.Basis.equiv_apply]
    simp [B,coe_basisOfLinearIndependentOfCardEqFinrank,hu]
  · intro i
    change (aeval (fun j=>sumSMulX (e (zhf j 1))) (z9v i)).IsHomogeneous 1
    rw [aeval_X]
    exact gwy _
theorem cYf {k :Type} [zrb k]
  (e :z3y (Fin 3) k ≃ₐ[k] z3y (Fin 3) k)
  (he : ∀ i,(e (z9v i)).IsHomogeneous 1) {p:z3y (Fin 3) k} {n:ℕ}
  (hp:p.IsHomogeneous n) : (e p).IsHomogeneous n:= by
 have h:aeval (fun i=>e (z9v i))=e.toAlgHom:= by
  apply algHom_ext
  intro i
  simp
 rw [← show e.toAlgHom p=e p from rfl,← h]
 simpa only [one_mul] using hp.aeval _ he
theorem cHE {A:Type} [za6 A] [zZE dF A]
   (d:Fin 3→A) {p:nW} (hp:p∈adu d) (n:ℕ) :
   homogeneousComponent n p∈adu d:= by
 classical
 let c (v :Fin 3 →₀ ℕ) (r :dF) :=
   algebraMap dF A r * ∏ i∈v.support,d i^v i
 have hmono (v :Fin 3 →₀ ℕ) (r :dF) :
     ab4 d (monomial v r)=zdM v.degree (c v r) := by
   rw [ab4,aeval_monomial,zpj,zsa]
   simp_rw [mul_pow]
   rw [zeY]
   simp_rw [← map_pow]
   rw [← map_prod,zX0,← mul_assoc,← map_mul,
     zoT]
   rfl
 have hparts :ab4 d (homogeneousComponent n p) =
     zdM n ((ab4 d p).coeff n) := by
   rw [show ab4 d p = ∑ v∈p.support,ab4 d (monomial v (p.coeff v)) by
     conv_lhs=>rw [p.as_sum]
     rw [map_sum]]
   rw [homogeneousComponent_apply,map_sum,zaW]
   simp only [hmono,zQm,← Finset.sum_filter,map_sum]
   apply zUo rfl
   intro v hv
   rw [(Finset.mem_filter.mp hv).2]
 change ab4 d p=0 at hp
 change ab4 d (homogeneousComponent n p)=0
 rw [hparts,hp,zO6,zQQ]
end
end ban
end
section
namespace cxY
noncomputable section
open aR B7 ap5 NS MvPolynomial
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
private theorem dzN {k σ:Type*} [zrb k]
   {I:znc (z3y σ k)} (hI:I.IsHomogeneous (homogeneousSubmodule σ k)) :
   lW I=I:= by
 apply le_antisymm
 · apply Ideal.span_le.mpr
   rintro _ ⟨p,n,hp,_,rfl⟩
   exact homogeneousComponent_mem_of_mem hI hp n
 · intro p hp
   rw [← sum_homogeneousComponent p]
   refine (lW I).sum_mem fun n _ => ?_
   have hn:homogeneousComponent n p∈I:=homogeneousComponent_mem_of_mem hI hp n
   have hh:=homogeneousComponent_isHomogeneous n p
   exact zCn ⟨_,n,hn,hh.totalDegree_le,(homogeneousComponent_eq_self hh).symm⟩
private theorem dIu {k σ:Type*} [zrb k] [Finite σ] [LinearOrder σ]
   [WellFoundedGT σ] (I:znc (z3y σ k))
   (hI:I.IsHomogeneous (homogeneousSubmodule σ k))
   (hd: (affineHilbertPolynomial I).natDegree≤1) (i:σ) :
   (affineHilbertPolynomial (I ⊔ zye {z9v i - 1})).natDegree=0:= by
 rcases Nat.eq_zero_or_pos (affineHilbertPolynomial I).natDegree with h | h
 · exact za7 ((natDegree_affineHilbertPolynomial_le_of_le
     (le_sup_left:I≤I ⊔ zye {z9v i - 1})).trans_eq h)
 · have hone : (affineHilbertPolynomial I).natDegree=1 := by omega
   simpa only [KL,dzN hI] using
     YT.bmo I hone i
private theorem arj {k L σ:Type*} [zrb k] [zrb L] [z85 σ]
   (f :k →+* L) (x :σ→L) (t:L) {p:z3y σ k} {n:ℕ}
   (hp:p.IsHomogeneous n) :eval₂ f (fun j=>t*x j) p=t^n*eval₂ f x p:= by
 classical
 rw [eval₂_eq',eval₂_eq',zxw]
 refine zUo rfl fun d hd => ?_
 have hdeg:d.degree=n:= by
   by_contra h
   exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero h)
 rw [show (∏ j:σ,(t*x j)^d j)=t^n * ∏ j:σ,x j^d j by
   simp only [mul_pow,zeY,zX0,
     ← zFi,hdeg]]
 ring
private theorem normalize_zero {k L σ:Type*} [zrb k] [zrb L] [zZE k L] [z85 σ]
   {I:znc (z3y σ k)} (hI:I.IsHomogeneous (homogeneousSubmodule σ k))
   {x :σ→L} (hx :x∈zeroLocus L I) {i:σ} (hi:x i≠0) :
   (fun j=>(x i)⁻¹*x j)∈zeroLocus L (I ⊔ zye {z9v i - 1}) := by
 change I ⊔ zye {z9v i - 1} ≤ zdq (aeval _).toRingHom
 apply sup_le
 · intro p hp
   change eval₂ (algebraMap k L) (fun j=>(x i)⁻¹*x j) p=0
   rw [← sum_homogeneousComponent p,eval₂_sum]
   refine zYF fun n _ => ?_
   rw [arj _ x _ (homogeneousComponent_isHomogeneous n p)]
   have hz :eval₂ (algebraMap k L) x (homogeneousComponent n p)=0 :=
     hx _ (homogeneousComponent_mem_of_mem hI hp n)
   rw [hz,mul_zero]
 · apply Ideal.span_le.mpr
   rintro _ (rfl :_=z9v i - 1)
   change eval₂ (algebraMap k L) (fun j=>(x i)⁻¹*x j) (z9v i - 1)=0
   rw [eval₂_sub,eval₂_X,eval₂_one]
   exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)
private theorem a4a {k L σ:Type*} [zrb k] [zrb L] [zZE k L]
  [IsAlgClosed k] [Finite σ] (J:znc (z3y σ k))
  (hJ: (affineHilbertPolynomial J).natDegree=0)
  {x :σ→L} (hx :x∈zeroLocus L J) (j:σ) : ∃ c:k,algebraMap k L c=x j:= by
 let:zAa k (z3y σ k ⧸ J) :=
  moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
 let e : (z3y σ k ⧸ J) →ₐ[k] L:=zTA J (aeval x) hx
 have h:IsIntegral k (x j) := by
  have hJX:=(zmn (R:=k) (zVv J (z9v j))).map e
  change IsIntegral k (aeval x (z9v j)) at hJX
  simpa only [aeval_X] using hJX
 apply h.mem_range_algHom_of_minpoly_splits (K:=k) _ (zNX k L)
 simpa only [zCp,zei] using
  IsAlgClosed.splits (minpoly k (x j))
private abbrev abB (k :Type*) [zrb k] :=AlgebraicClosure (FractionRing k[X])
private def aHY (k :Type*) [zrb k] :k[X] →+* abB k :=
 (algebraMap (FractionRing k[X]) (abB k)).comp (algebraMap k[X] (FractionRing k[X]))
private def qK (k :Type*) [zrb k] :k →+* abB k :=
 (algebraMap (FractionRing k[X]) (abB k)).comp (algebraMap k (FractionRing k[X]))
private def a4v (k :Type*) [zrb k] (n:ℕ) :
   z3y (Fin n) (FractionRing k[X]) :=
 ∑ j:Fin n,C ((algebraMap k[X] (FractionRing k[X]) z7y)^j.val)*z9v j
private theorem d2m {k :Type*} [zrb k] {n:ℕ} (a :Fin n→k) :
   aeval (qK k ∘ a) (a4v k n) =
     aHY k (∑ j:Fin n,zdM j.val (a j)) := by
 classical
 unfold a4v
 rw [map_sum,map_sum]
 refine zUo rfl fun j _ => ?_
 rw [← zoT]
 simp only [map_mul,aeval_C,aeval_X,z3s,qK,aHY,
   zQb,map_pow]
 rw [← zrE,
   ← zG3 k k[X] (FractionRing k[X]),mul_comm]
private theorem efJ (k :Type*) [zrb k] (n:ℕ) :
   (a4v k n).IsHomogeneous 1 :=
 (homogeneousSubmodule (Fin n) (FractionRing k[X]) 1).sum_mem fun j _ =>
   isHomogeneous_C_mul_X _ j
private theorem efV {k :Type*} [zrb k] [IsAlgClosed k] {n:ℕ}
    (I:znc (z3y (Fin n) k))
    (hI:I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    (hd: (affineHilbertPolynomial I).natDegree≤1) (i:Fin n) :
    z9v i ∈
      (I.map (zDK (algebraMap k (FractionRing k[X]))) ⊔
        zye {a4v k n}).radical:= by
  classical
  rw [← vanishingIdeal_zeroLocus_eq_radical (K:=abB k)]
  apply mem_vanishingIdeal_iff.mpr
  intro x hx
  rw [aeval_X]
  by_contra hi
  let:zZE k (abB k) :=(qK k).toAlgebra
  have hxI:x∈zeroLocus (abB k) I:= by
    intro p hp
    have h:=hx _ (zKg (z7X
      (zDK (algebraMap k (FractionRing k[X]))) hp))
    rw [aeval_def,eval₂_map] at h
    exact h
  have hb:=normalize_zero hI hxI hi
  choose a ha using fun j=>a4a _ (dIu I hI hd i) hb j
  have he :qK k ∘ a=fun j=>(x i)⁻¹*x j:=funext ha
  have hai:a i≠0:= by
    intro h
    have h' := ha i
    change qK k (a i)=(x i)⁻¹*x i at h'
    rw [h,map_zero,inv_mul_cancel₀ hi] at h'
    exact zero_ne_one h'
  have hv :=hx (a4v k n) (zs0 (z5J _))
  have hv' : aeval (qK k ∘ a) (a4v k n)=0:= by
    rw [he,aeval_def,arj _ x _ (efJ k n),← aeval_def,hv,mul_zero]
  rw [d2m] at hv'
  have hinj:zq4 (aHY k) :=
    (algebraMap (FractionRing k[X]) (abB k)).injective.comp (zxb _ _)
  have hp:=hinj (hv'.trans (aHY k).map_zero.symm)
  have hc:=congrArg (fun p:k[X]=>p.coeff i.val) hp
  rw [zaW,zi6 i] at hc
  · exact hai (by simpa only [z2j,zO6] using hc)
  · intro j _ hj
    exact Polynomial.coeff_monomial_of_ne _ (fun h=>hj (z0e h.symm))
  · simp
theorem proof :ap5.c1 := by
 intro I hI hd i
 simpa only [aAE,oV,adF,KT,a4v,PV,
  zCM,z4o,one_mul,Nat.sub_zero] using
  efV I hI hd i
end
end cxY
end
section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000
namespace aKt
noncomputable section
open MvPolynomial aR dN rW E7
open scoped Polynomial nonZeroDivisors
private theorem bW0 {k E σ:Type} [zrb k] [zrb E] [zZE k E]
    (R:znc (z3y σ k)) [R.IsPrime] [(abk (E :=E) R).IsPrime]
    {a :σ} {z :E} (hz :Transcendental k z) (ha :z9v a∉R) :
    let H :=abk (E :=E) R
    ∃ inc:FO R a →+* FO H a,
      z9v a∉H ∧
      inc.comp (algebraMap k (FO R a)) =
        (algebraMap E (FO H a)).comp (algebraMap k E) ∧
      (∀ i,inc (BQ R a i)=BQ H a i) ∧
      zq4 (zqf inc (algebraMap E (FO H a) z)) := by
  let H :=abk (E :=E) R
  let j:JP R →+* JP H :=zJ1 (bYy R hz)
  have hjmk (p:z3y σ k) :
      j (algebraMap (MG R) (JP R) (zVv R p)) =
        algebraMap (MG H) (JP H)
          (zVv H (zDK (algebraMap k E) p)) :=
    zi7 (M:=(MG R)⁰) (T:=(MG H)⁰) _ _
  have hj (i:σ) :j (SR R i)=SR H i:= by
    simpa only [SR,z7N] using hjmk (z9v i)
  have ha' : z9v a∉H := by
    intro h
    have hzero :SR H a=0:= by
      simp [SR,Ideal.Quotient.eq_zero_iff_mem.mpr h]
    exact bnL ha (j.injective (by rw [hj,hzero,map_zero]))
  have hj' (i:σ) :
      j ((BQ R a i:FO R a) :JP R) =
        (BQ H a i:JP H) := by rw [cFa,cFa,map_div₀,hj,hj]
  let Fresh:=FO H a
  let Old:=FO R a
  let jk :Old →ₐ[k] JP H :=
    { toRingHom:=j.comp (FO R a).val.toRingHom
      commutes' := by
        intro x
        change j (algebraMap k (JP R) x)= _
        change j (algebraMap (MG R) (JP R) (zVv _ (znf x)))= _
        rw [hjmk,zpw]
        rfl }
  let L:IntermediateField k (JP H) :=(FO H a).restrictScalars k
  have hle : (⊤ : IntermediateField k Old)≤L.comap jk := by
    rw [← bcs R a]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    change jk (BQ R a i)∈L
    rw [show jk (BQ R a i)=(BQ H a i:JP H) from hj' i]
    exact (BQ H a i).property
  let inc:Old →+* Fresh:=jk.toRingHom.codRestrict Fresh.toSubfield
    (fun x=>hle (show x∈(⊤ : IntermediateField k Old) from trivial))
  have hinc (i:σ) :inc (BQ R a i)=BQ H a i :=
    Subtype.ext (hj' i)
  have hind:zq4
      (zqf inc (algebraMap E Fresh z)) := by
    have he : (FO H a).val.toRingHom.comp
        (zqf inc (algebraMap E Fresh z)) =
        (zqf j (algebraMap E (JP H) z)).comp
          (zhd (FO R a).val.toRingHom) := by
      apply z86
      · intro x
        simp only [zQb,z4Q,zJU,
          zKC,zrL]
        rfl
      · simp only [zQb,z4Q,zC9,
          zKC,zSo]
        rfl
    apply Function.Injective.of_comp (f := fun z :Fresh=>(z :JP H))
    change zq4 ((FO H a).val.toRingHom.comp
      (zqf inc (algebraMap E Fresh z)))
    rw [he]
    exact (dON R hz).comp
      (zTo _ (FO R a).val.injective)
  refine ⟨inc,ha',?_,hinc,hind⟩
  apply zz4
  intro x
  exact Subtype.ext (jk.commutes x)
private theorem SZ:zq4 dN.j8 :=
 (algebraMap lN GeoField).injective.comp
   (zxb ao[X] lN)
private theorem b3U [zZE ao GeoField]
   (hc:algebraMap ao GeoField=ni) :
   Transcendental ao rI:= by
 apply transcendental_iff_injective.mpr
 have h: (zEU rI:ao[X] →ₐ[ao] GeoField).toRingHom =
     dN.j8:= by
   apply z86
   · intro c
     change (zEU rI:ao[X] →ₐ[ao] GeoField)
         (z1z c)=ni c
     rw [z8q]
     exact zLs hc c
   · change (zEU rI:ao[X] →ₐ[ao] GeoField)
         z7y=rI
     exact zw0 _
 change zq4 (zEU rI :
   ao[X] →ₐ[ao] GeoField).toRingHom
 rw [h]
 exact SZ
private theorem b9m {n:ℕ} {L:Type} [zrb L] [DecidableEq L]
  (u:Fin n→L) (a :Fin n) (ha :u a=1)
  (hz : ∀ i,a< i→u i=0) :
  (zDW n u).Monic∧(zDW n u).natDegree<n:= by
 have hcoeff :=zPX u a.isLt
 have hle : (zDW n u).natDegree≤a.val := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  by_cases h:m<n
  · rw [zPX u h]
    exact hz ⟨m,h⟩ hm
  · exact Polynomial.ofFn_coeff_eq_zero_of_ge u (by omega)
 exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one a.val hle (hcoeff.trans ha),
  hle.trans_lt a.isLt⟩
private theorem bX1 {n:ℕ} {F L:Type}
  [zrb F] [zrb L] [DecidableEq F] (j:F →+* L) (u:Fin n→F) :
  OX (N :=n) j (zDW n u)=j ∘ u:= by
 funext i
 exact congrArg j (zPX u i.isLt)
set_option backward.isDefEq.respectTransparency false in
theorem proof :E7.c1 := by
 classical
 intro R hR hprime hhom hdim
 let:R.IsPrime :=hR
 let:zZE ao GeoField:=ni.toAlgebra
 let: (abk (E :=GeoField) R).IsPrime :=hprime
 have hz :=b3U rfl
 obtain ⟨a,ha,hlast⟩:=bFy R hdim
 obtain ⟨inc,ha',hconstants,hinc,hind⟩:=bW0 (E :=GeoField) R hz ha
 let H :=abk (E :=GeoField) R
 let Old:=FO R a
 let Fresh:=FO H a
 let f :Old[X] :=zDW bf (BQ R a)
 have hf :=b9m (BQ R a) a (bWY ha) (by
   intro i hi
   apply Subtype.ext
   change SR R i/SR R a=0
   simp [SR,Ideal.Quotient.eq_zero_iff_mem.mpr (hlast i hi)])
 have htuple :OX (N :=bf) inc f=BQ H a :=
   (bX1 inc (BQ R a)).trans (funext hinc)
 have hhom' := cUQ (algebraMap ao GeoField) hhom
 have hd' : dimension H=2 := by
   change (zIU (R.map (zDK
     (algebraMap ao GeoField)))).natDegree= _
   rw [Ey.ZI]
   exact hdim
 obtain ⟨hold,_⟩:=bCy R a hhom ha hdim
 obtain ⟨hfresh,hnonconstant⟩:=bCy H a hhom' ha' hd'
 have heq :H=SQ GeoField (OX (N :=bf) inc f) :=
   (bYw hhom' ha').symm.trans (congrArg (SQ GeoField) htuple).symm
 have hgen:IntermediateField.adjoin GeoField
     (zxp (OX (N :=bf) inc f)) = ⊤ := by
   rw [htuple]
   exact bcs H a
 have hnon : ∃ i:Fin bf,Transcendental GeoField (OX inc f i) :=
   htuple.symm ▸ hnonconstant
 exact ⟨{
   Old:=Old
   Fresh:=Fresh
   oldCurve :=hold
   aDk :=hfresh
   Fl:=inc
   constants :=hconstants
   independent:=hind
   polynomial:=f
   monic:=hf.1
   degree_le :=Nat.lt_succ_iff.mp hf.2
   equation :=heq
   generates :=hgen
   nonconstant:=hnon }⟩
end
end aKt
end
section
namespace ban
noncomputable section
open B7 Ey Pw MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false
abbrev bah {A:Type} [za6 A] [zZE dF A] (d:Fin 3→A) :=
 nW ⧸ adu d
abbrev brj {A:Type} [za6 A] [zZE dF A] (d:Fin 3→A) :
  bah d →ₐ[dF] A[X] :=
 zdc (ab4 d)
theorem cVS {A:Type} [za6 A] [zZE dF A]
  (d:Fin 3→A) :zq4 (brj d) :=
 zvo _
theorem dOP {A:Type} [za6 A] [zZE dF A]
  (d:Fin 3→A) (L:Fin 2→nW) :
  adv d L=(brj d).comp (afO L (adu d)) :=
 rfl
private theorem eaY {k :Type} [zrb k]
  {J:znc (z3y (Fin 3) k)}
  (g g' : z3y (Fin 2) k →ₐ[k] (z3y (Fin 3) k ⧸ J))
  (hg:g.Finite) (hg' : g'.Finite) (hi:zq4 g') :
  Function.Injective g:= by
 let I:znc (z3y (Fin 2) k) :=zdq g
 have hdim: (affineHilbertPolynomial J).natDegree=2 := by
  simpa using natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g' hg' hi
 let q:=zvR k I
 let j:=zdc g
 have hj:j.comp q=g:=rfl
 have hfin:j.Finite :=AlgHom.Finite.of_comp_finite (f :=q) (by rwa [hj])
 have hdim' := natDegree_affineHilbertPolynomial_eq_of_finite_of_injective j hfin
  (zvo g)
 by_contra hn
 have hnb:I ≠ ⊥ := fun hb=>hn ((zli g.toRingHom).mpr hb)
 obtain ⟨p,hp,hp0⟩:=Submodule.exists_mem_ne_zero_of_ne_bot hnb
 have hsmall:=natDegree_affineHilbertPolynomial_le_of_mem hp0 hp
 change (affineHilbertPolynomial J).natDegree=(affineHilbertPolynomial I).natDegree at hdim'
 rw [← hdim',hdim] at hsmall
 simp at hsmall
theorem epP {J:znc nW} {L M:Fin 2→nW}
  (hL:agE L J) (hM:agE M J)
  (hi:zq4 (afO M J)) :
  zq4 (afO L J) :=
 eaY (afO L J) (afO M J) hL.2 hM.2 hi
theorem eJA {B:Type} [za6 B] [zZE dF B]
  (φ:l5 →ₐ[dF] B) :
  letI:zZE l5 B:=φ.toRingHom.toAlgebra
  azK φ=zsE l5 B:= by
 letI:zZE l5 B:=φ.toRingHom.toAlgebra
 let f :=zUP l5 MY B 1
 exact (IsFractionRing.finrank_right_eq l5 MY (aPb φ)).trans
  (IsLocalizedModule.finrank_eq (nonZeroDivisors l5) f le_rfl)
theorem eJx {B:Type} [za6 B] [ztn B] [zZE dF B]
  (φ:l5 →ₐ[dF] B) (hi:zq4 φ) :
  Nontrivial (aPb φ) := by
 letI:zZE l5 B:=φ.toRingHom.toAlgebra
 let f :=zUP l5 MY B 1
 refine (show zq4 f from ?_).nontrivial
 apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors l5) f).2
 intro c x y h
 change φ c*x=φ c*y at h
 have hc:φ c≠φ 0:=hi.ne (mem_nonZeroDivisors_iff_ne_zero.mp c.property)
 rw [map_zero] at hc
 exact mul_left_cancel₀ hc h
def aOH {R S:Type} [za6 R] [za6 S] (g:R →+* S) :ℕ :=
 @zsE R S _ _ g.toAlgebra.toModule
private theorem eyR {R S T:Type}
  [za6 R] [za6 S] [za6 T] [ztn T]
  (g:R →+* S) (f :S →+* T) (hf :zq4 f) :
  aOH (f.comp g)=aOH g*aOH f := by
 letI:zZE R S:=g.toAlgebra
 letI:zZE S T:=f.toAlgebra
 letI:zZE R T:=(f.comp g).toAlgebra
 haveI:zsf R S T:=IsScalarTower.of_algebraMap_eq' rfl
 haveI:FaithfulSMul S T:=(faithfulSMul_iff_algebraMap_injective S T).mpr hf
 exact (Module.finrank_mul_finrank' (R:=R) (S:=S) T).symm
theorem eJz {B C:Type}
  [za6 B] [za6 C] [ztn C] [zZE dF B] [zZE dF C]
  (g:l5 →ₐ[dF] B) (f :B →ₐ[dF] C) (hf :zq4 f) :
  azK (f.comp g)=aOH g.toRingHom*aOH f.toRingHom:= by
 exact (eJA (f.comp g)).trans
  (eyR g.toRingHom f.toRingHom hf)
end
end ban
end
section
namespace cx8
noncomputable section
open B7 axd MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private def affineMap (P:znc jo) (g d:nW) (h:XP P g d) :
  (nW ⧸ zye {g}) →ₐ[dF] (mK ⧸ oV P) :=
 zwL _ tO h.image.ge
private def avp :
  z3y (Option (Fin 3)) dF →ₐ[dF]
    z3y (Option rS) dF :=
 aeval fun
  | none=>MvPolynomial.X none
  | some i=>rename some (tO (MvPolynomial.X i))
private theorem ev4 (f :nW) :
  avp (rename some f)=rename some (tO f) := by
 have he :avp.comp (rename some)=(rename some).comp tO:= by
  apply zpH
  intro i
  simp [avp]
 exact zmU he f
private theorem gmq {K σ:Type} [zrb K] [z85 σ]
   (J:znc (z3y σ K)) (c:σ→K) :
   TS J (rename some (∑ a,C (c a)*z9v a)) =
     z1z (zVv J (∑ a,C (c a)*z9v a))*Polynomial.X:= by
 simp only [map_sum,map_mul,rename_C,rename_X,TS,aeval_X,aeval_C,
   zkq]
 apply zUo rfl
 intro a _
 rw [← mul_assoc]
 rfl
private theorem gmp (J:znc mK) (i:Fin 3) :
  TS J (rename some (tO (z9v i))) =
   z1z (zVv J (tO (z9v i)))*Polynomial.X:= by
 simp only [tO,aeval_X,KT]
 exact gmq J _
private theorem c5D (P:znc jo) (g d:nW)
   (h:XP P g d) :
   (TS (oV P)).comp avp =
     (z0c (affineMap P g d h)).comp (TS (zye {g})) := by
 apply zpH
 intro i
 cases i with
 | none =>
   simp [avp,TS]
 | some i =>
   simpa [avp,TS,affineMap] using gmp (oV P) i
private theorem dLV (P:znc jo) (g d:nW)
  (h:XP P g d) :
  JA (zye {g})≤(JA (oV P)).comap avp:= by
 intro f hf
 change TS (oV P) (avp f)=0
 have h0:TS (zye {g}) f=0:=hf
 have hc:=zmU (c5D P g d h) f
 change TS (oV P) (avp f) =
  z0c (affineMap P g d h) (TS (zye {g}) f) at hc
 rw [hc,h0,map_zero]
private def qR (P:znc jo) (g d:nW) (h:XP P g d) :
  Closure (zye {g}) →ₐ[dF] Closure (oV P) :=
 zwL _ avp (dLV P g d h)
private def aym {K σ:Type} [zrb K] (I:znc (z3y σ K)) :
  Closure I →ₐ[K] zM1 (z3y σ K ⧸ I) :=
 zdc (TS I)
private theorem dLR {K σ:Type} [zrb K] (I:znc (z3y σ K)) :
  zq4 (aym I) :=
 zvo _
private theorem cLC {K σ:Type} [zrb K] (I:znc (z3y σ K)) :
  aym I (Zu I)=zdM 1 1 := by
 change TS I (z9v none)= _
 simp only [TS,aeval_X,Polynomial.monomial_one_one_eq_X]
private theorem cLE {K σ:Type} [zrb K] (I:znc (z3y σ K)) (i:σ) :
  aym I (zVv (JA I) (z9v (some i))) =
   zdM 1 (zVv I (z9v i)) := by
 change TS I (z9v (some i))= _
 simp only [TS,aeval_X,Polynomial.C_mul_X_eq_monomial]
private theorem d08 (P:znc jo) (g d:nW)
  (h:XP P g d) (q:Closure (zye {g})) :
  aym (oV P) (qR P g d h q) =
    z0c (affineMap P g d h) (aym (zye {g}) q) := by
 obtain ⟨f,rfl⟩:=zld q
 exact zmU (c5D P g d h) f
private theorem aUr {K σ:Type} [zrb K]
   (I:znc (z3y σ K)) (f :z3y σ K) :
   ∃ (q:Closure I) (n:ℕ),
     aym I q=zdM n (zVv I f) := by
 induction f using z5i with
 | C c =>
   refine ⟨algebraMap K (Closure I) c,0,?_⟩
   rw [zKk,Polynomial.monomial_zero_left,zpj]
   rfl
 | add f v hf hv =>
   obtain ⟨p,m,hp⟩:=hf
   obtain ⟨q,n,hq⟩:=hv
   refine ⟨Zu I ^n*p+Zu I ^m*q,m+n,?_⟩
   simp only [map_add,map_mul,map_pow,cLC,hp,hq,zCL,
     zva,one_mul,one_pow]
   rw [zg2 n m,← map_add]
 | mul_X f i hf =>
   obtain ⟨p,m,hp⟩:=hf
   refine ⟨p* zVv (JA I) (z9v (some i)),m+1,?_⟩
   simp only [map_mul,hp,cLE,zva]
private theorem fU0 {K σ:Type} [zrb K] {A:Type} [za6 A]
   [zZE K A] (J:znc (z3y σ K)) (s :A →ₐ[K] Closure J) (b:A)
   (hvars : ∀ i:Option σ,∃ q:A,∃ m:ℕ,
     s q=s b^m* zVv (JA J) (z9v i)) :
   ∀ a :Closure J,∃ q:A,∃ m:ℕ,s q=s b^m*a := by
 intro a
 obtain ⟨f,rfl⟩:=zld a
 induction f using z5i with
 | C c =>
   refine ⟨algebraMap K A c,0,?_⟩
   rw [zKk,pow_zero,one_mul]
   rfl
 | add f v hf hv =>
   obtain ⟨p,m,hp⟩:=hf
   obtain ⟨q,n,hq⟩:=hv
   refine ⟨b^n*p+b^m*q,m+n,?_⟩
   simp only [map_add,map_mul,map_pow,hp,hq,pow_add]
   ring
 | mul_X f i hf =>
   obtain ⟨p,m,hp⟩:=hf
   obtain ⟨q,n,hq⟩:=hvars i
   refine ⟨p*q,m+n,?_⟩
   simp only [map_mul,hp,hq,pow_add]
   ring
theorem proof :axd.c3:= by
  intro P g d h
  let I:znc nW:=zye {g}
  let J:=oV P
  let s :Closure I →ₐ[dF] Closure J:=qR P g d h
  have hW:s (Zu I)=Zu J:= by
    change zVv (JA J) (avp (z9v none))= _
    simp [avp,Zu]
  refine ⟨s,hW,?_,?_⟩
  · intro f
    change zVv (JA J) (avp (rename some f))= _
    exact congrArg (zVv (JA J)) (ev4 f)
  obtain ⟨D,r,hDr⟩:=aUr I d
  let b:=Zu I*D
  let δ:=zVv J (tO d)
  have hδ:δ≠0:= by
    rw [show δ=zVv J (tO d) from rfl,ne_eq,
      z1Q]
    intro hd
    apply h.regular_open
    rw [← h.image]
    exact hd
  have transfer (q:Closure I) (v :nW) (n:ℕ)
      (hq:aym I q=zdM n (zVv I v)) :
      aym J (s q)=zdM n (zVv J (tO v)) := by
    change aym J (qR P g d h q)= _
    rw [d08,hq,Polynomial.mapAlgHom_monomial]
    rfl
  have hD:aym J (s D)=zdM r δ:=transfer D d r hDr
  have hw:aym J (s (Zu I))=zdM 1 1 := by
    rw [hW]
    exact cLC J
  have hb:s b≠0:= by
    intro hzero
    have hz :=congrArg (aym J) hzero
    simp only [b,map_mul,hw,hD,zva,one_mul,map_zero] at hz
    exact hδ ((Polynomial.monomial_eq_zero_iff δ (1+r)).mp hz)
  refine ⟨b,hb,fU0 J s b ?_⟩
  intro i
  cases i with
  | none =>
    refine ⟨Zu I,0,?_⟩
    change s (Zu I)=s b^0*Zu J
    simpa only [pow_zero,one_mul] using hW
  | some i =>
    obtain ⟨v,m,hv⟩:=h.recover i
    obtain ⟨V,n,hVn⟩:=aUr I v
    have ha :zVv J (tO v) =
        δ^m* zVv J (z9v i) := by
      have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr hv
      simp only [map_sub,map_mul,map_pow,sub_eq_zero] at hz
      exact hz.symm
    have hV:=(transfer V v n hVn).trans (congrArg (zdM n) ha)
    refine ⟨Zu I ^(m*(r+1)+1)*D^n*V,m+n,?_⟩
    apply dLR J
    simp only [b,map_mul,map_pow,hw,hD,hV,cLE,
      zCL,zva,one_mul,one_pow]
    apply congrArg₂ (fun k c=>(zdM k c:zM1 (mK ⧸ J)))
    · ring
    · ring
end
end cx8
end
section
namespace bzv
noncomputable section
open MvPolynomial B7 Ey Pw
open scoped Polynomial
set_option maxHeartbeats 1000000
private theorem cZI {F B σ:Type} [zrb F] [za6 B] [zZE F B]
  (x :σ→F) (p:z3y σ F) :
  aeval (fun i=>algebraMap F B (x i)) p=algebraMap F B (eval x p) := by
 exact (comp_aeval_apply x (zNX F B) p).symm
private theorem gsH {F A:Type} [zrb F] [za6 A] [zZE F A]
   (d:Fin 3→A) (hd:zye (zxp d) = ⊤)
   (t:F) {p:z3y (Fin 3) F} {n:ℕ}
   (hp:p.IsHomogeneous n) (hrel :aeval d p=0) (ht:eval ![0,t,1] p≠0) :
   IsUnit (zVv (zye {d 0}) (d 1-algebraMap F A t*d 2)) := by
 let D:=A ⧸ zye {d 0}
 let ρ:A →ₐ[F] D:=zvR F _
 let w:A:=d 1-algebraMap F A t*d 2
 change IsUnit (ρ w)
 by_contra hn
 obtain ⟨N,hN,hle⟩:=zsl (zye {ρ w})
   (fun h=>hn (Ideal.span_singleton_eq_top.mp h))
 let _:N.IsMaximal:=hN
 let E :=D ⧸ N
 let π:A →ₐ[F] E :=(zvR F N).comp ρ
 have h0:π (d 0)=0:= by
   have hρ:ρ (d 0)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (z5J _)
   simp [π,hρ]
 have hw:π w=0 :=
   Ideal.Quotient.eq_zero_iff_mem.mpr (hle (z5J _))
 have h1 :π (d 1)=algebraMap F E t*π (d 2) := by
   simpa [w,map_sub,map_mul,sub_eq_zero] using hw
 have hx : (fun i=>π (d i)) =
     fun i=>π (d 2)*algebraMap F E ((![0,t,1] :Fin 3→F) i) := by
   funext i
   fin_cases i <;> simp [h0,h1,mul_comm]
 have h:=congrArg π hrel
 rw [comp_aeval_apply,map_zero,hx,bqW hp,cZI] at h
 have h2 :π (d 2)=0:= by
   by_contra h2
   exact (mul_ne_zero (pow_ne_zero _ h2) ((map_ne_zero (algebraMap F E)).2 ht)) h
 have hle' : zye (zxp d)≤zdq π.toRingHom :=
   Ideal.span_le.mpr (by
     rintro _ ⟨i,rfl⟩
     change π (d i)=0
     fin_cases i <;> simp [h0,h1,h2])
 have hbad:π 1=0:=hle' (by rw [hd]; trivial)
 simp at hbad
private theorem d2D {F:Type} [zrb F] [Infinite F]
   {p:z3y (Fin 2) F} {n:ℕ}
   (hp:p.IsHomogeneous n) (hrest: (finSuccEquiv F 1 p).coeff 0≠0) :
   eval ![0,1] p≠0:= by
 intro hzero
 apply hrest
 apply zjN
 intro x
 have hvx : (fun i=>x 0*((![0,1] :Fin 2→F) i))=z4W 0 x := by
   funext i
   fin_cases i
   · simp
   · change x 0*1=z4W (α:= fun _=>F) 0 x (0:Fin 1).succ
     rw [zVG,mul_one]
 have he :=bqW hp (![0,1] :Fin 2→F) (x 0)
 rw [hvx,aeval_eq_eval,aeval_eq_eval,hzero,mul_zero,
   eval_eq_eval_mv_eval',← zTt,z0b] at he
 simpa using he
private theorem eLm {F A:Type} [zrb F] [Infinite F] [za6 A] [ztn A]
   [zZE F A] (v w:A) (hv :v≠0) (hvu : ¬ IsUnit v)
   (hw:IsUnit (zVv (zye {v}) w)) :
   zq4 (aj1 F v w) := by
 classical
 by_contra h
 have heq :nY (F:=F) (![v,w] :Fin 2→A)=aj1 F v w:= by
   apply zpH
   intro i
   fin_cases i <;> simp [nY,aj1]
 have h' : ¬ zq4 (nY (F:=F) (![v,w] :Fin 2→A)) := by
   rwa [heq]
 obtain ⟨p,n,hp,hrel,hrest⟩ :=
   c79 (F:=F) (m:=1) (![v,w] :Fin 2→A) hv h'
 let D:=A ⧸ zye {v}
 let _:Nontrivial D:=Ideal.Quotient.nontrivial_iff.mpr
   (fun h=>hvu (Ideal.span_singleton_eq_top.mp h))
 let ρ:A →ₐ[F] D:=zvR F _
 have hv' : ρ v=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (z5J _)
 have hmap : (fun i=>ρ ((![v,w] :Fin 2→A) i)) =
     fun i=>ρ w*algebraMap F D ((![0,1] :Fin 2→F) i) := by
   funext i
   fin_cases i <;> simp [hv']
 have hr :=congrArg ρ hrel
 rw [comp_aeval_apply,map_zero,hmap,bqW hp,cZI] at hr
 have hunit :IsUnit (ρ w) :=hw
 exact ((map_ne_zero (algebraMap F D)).2 (d2D hp hrest))
   ((hunit.pow n).mul_left_cancel (hr.trans (mul_zero _).symm))
private def aWh (t:dF) :Fin 2→nW :=
 ![z9v 0,z9v 1 - C t*z9v 2]
private theorem eJy (t:dF) (i:Fin 2) :
   (aWh t i).IsHomogeneous 1 := by
 fin_cases i
 · exact isHomogeneous_X dF 0
 · exact (isHomogeneous_X dF (1 :Fin 3)).sub
     ((isHomogeneous_C (Fin 3) t).mul (isHomogeneous_X dF 2))
private def J6 (t:dF) :Fin 3→nW :=
 ![z9v 1,z9v 2+C t*z9v 0,z9v 0]
private theorem gp7 (t:dF) (i:Fin 3) :
   (J6 t i).IsHomogeneous 1 := by
 fin_cases i
 · exact isHomogeneous_X dF 1
 · exact (isHomogeneous_X dF (2 :Fin 3)).add
     ((isHomogeneous_C (Fin 3) t).mul (isHomogeneous_X dF 0))
 · exact isHomogeneous_X dF 0
private theorem gG0 (t:dF) {p:nW} {n:ℕ}
   (hp:p.IsHomogeneous n) (ht:eval ![0,t,1] p≠0) :
   IsUnit (finSuccEquiv dF 2 (aeval (J6 t) p)).leadingCoeff := by
 let q:nW:=aeval (J6 t) p
 let P:=finSuccEquiv dF 2 q
 have hq:q.IsHomogeneous n:= by
   simpa [q] using hp.aeval (J6 t) (gp7 t)
 have hn:P.natDegree≤n:= by
   rw [show P=finSuccEquiv dF 2 q from rfl,natDegree_finSuccEquiv]
   exact (degreeOf_le_totalDegree _ _).trans hq.totalDegree_le
 have heq :eval (z4W 1 0) q=eval ![0,t,1] p:= by
   change (aeval (z4W 1 0:Fin 3→dF)) (aeval (J6 t) p)= _
   rw [comp_aeval_apply]
   let a :Fin 3→dF:=z4W 1 0
   have h1 :a 1=0:=zVG (α:= fun _=>dF) 1 (0:Fin 2→dF) 0
   have h2 :a 2=0:=zVG (α:= fun _=>dF) 1 (0:Fin 2→dF) 1
   have h0:a 0=1 :=zhe (α:= fun _=>dF) _ _
   have hx : (fun i=>eval a (J6 t i)) = ![0,t,1] := by
     funext i
     fin_cases i <;> simp [J6,h0,h1,h2]
   change aeval (fun i=>eval a (J6 t i)) p=aeval ![0,t,1] p
   rw [hx]
 have hz (i:ℕ) (hi:i∈z4x n) :constantCoeff (P.coeff i)=0:= by
   have hil:=Finset.mem_range.mp hi
   exact (hq.finSuccEquiv_coeff_isHomogeneous i (n - i) (by omega)).coeff_eq_zero (by simp; omega)
 have heval :constantCoeff (P.coeff n)=eval ![0,t,1] p:= by
   rw [← heq,eval_eq_eval_mv_eval',Polynomial.eval_one_map,eval_zero]
   change _=constantCoeff (P.eval 1)
   rw [Polynomial.eval_eq_sum_range' (by omega :P.natDegree<n+1)]
   simp [Finset.sum_range_succ,zYF hz]
 have htop:P.coeff n=C (eval ![0,t,1] p) := by
   rw [← heval]
   have hhom:=hq.finSuccEquiv_coeff_isHomogeneous n 0 (add_zero n)
   exact (homogeneousComponent_eq_self hhom).symm.trans (homogeneousComponent_zero _)
 have hdegree :P.natDegree=n:=hn.antisymm <|
   Polynomial.le_natDegree_of_ne_zero (by rw [htop]; simpa using ht)
 change IsUnit P.leadingCoeff
 rw [z4w,hdegree,htop]
 exact ht.isUnit.map C
private theorem eaT {R S:Type} [za6 R] [za6 S]
  (g:R →+* S) (z :S) (Q:R[X]) (hm:Q.Monic) (hQ:Q.eval₂ g z=0)
  (hE : ∀ y :S,∃ x :R[X],x.eval₂ g z=y) :g.Finite := by
 let f :=AdjoinRoot.lift g z hQ
 have hf :zpX f := by
  intro y
  obtain ⟨x,hx⟩:=hE y
  exact ⟨AdjoinRoot.mk Q x,(AdjoinRoot.lift_mk hQ x).trans hx⟩
 rw [← AdjoinRoot.lift_comp_of hQ]
 exact zfr (zO7 f hf)
  (RingHom.finite_algebraMap.mpr hm.finite_adjoinRoot)
private theorem eaP {A:Type} [za6 A] [zZE dF A]
    (d:Fin 3→A) (t:dF) {p:nW} {n:ℕ}
    (hp:p.IsHomogeneous n) (hrel :aeval d p=0) (ht:eval ![0,t,1] p≠0) :
    agE (aWh t) (adu d) := by
  refine ⟨eJy t,?_⟩
  let J:=adu d
  let g:=afO (aWh t) J
  let z :=zVv J (z9v 2)
  let E :l5[X] →ₐ[dF] nW ⧸ J :=
    Polynomial.eval₂AlgHom g z (fun a=> by
      change g a*z=z*g a
      exact mul_comm (g a) z)
  let ψ:nW →ₐ[dF] l5[X] :=
    (finSuccEquiv dF 2).toAlgHom.comp (aeval (J6 t))
  have hEC (a :l5) :E (z1z a)=g a :=zJU _ _
  have hEX:E z7y=z :=zC9 _ _
  have hψ (i:Fin 3) :ψ (z9v i)=finSuccEquiv dF 2 (J6 t i) := by
    simp [ψ]
  have hg (i:Fin 2) :g (z9v i)=zVv J (aWh t i) := by
    simp [g,afO]
  have hX1 :finSuccEquiv dF 2 (z9v 1)=z1z (z9v 0) :=
    finSuccEquiv_X_succ (j:=0)
  have hX2 :finSuccEquiv dF 2 (z9v 2)=z1z (z9v 1) :=
    finSuccEquiv_X_succ (j:=1)
  have hscalar :E (finSuccEquiv dF 2 (C t))=zVv J (C t) :=
    ((E.comp (finSuccEquiv dF 2).toAlgHom).commutes t).trans
      ((zvR dF J).commutes t).symm
  have hcomp:E.comp ψ=zvR dF J:= by
    apply zpH
    intro i
    change E (ψ (z9v i))=zVv J (z9v i)
    rw [hψ]
    fin_cases i
    · change E (finSuccEquiv dF 2 (z9v 1))= _
      rw [hX1,hEC,hg]
      rfl
    · change E (finSuccEquiv dF 2 (z9v 2+C t*z9v 0))= _
      rw [map_add,map_mul,hX2,finSuccEquiv_X_zero,map_add,map_mul,hEC,hg,hEX,hscalar]
      change zVv J (z9v 1 - C t*z9v 2) +
        zVv J (C t)* zVv J (z9v 2)= _
      rw [← map_mul,← map_add,sub_add_cancel]
      rfl
    · change E (finSuccEquiv dF 2 (z9v 0))= _
      rw [finSuccEquiv_X_zero,hEX]
      rfl
  have hE :zpX E := by
    intro y
    obtain ⟨x,hx⟩:=zld y
    exact ⟨ψ x,(zmU hcomp x).trans hx⟩
  let P:=ψ p
  have hP:E P=0:= by
    change (E.comp ψ) p=0
    rw [hcomp]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact show nY d p=0 from by
      rw [bNn d hp,hrel,zQQ]
  have hu:IsUnit P.leadingCoeff :=gG0 t hp ht
  let Q:=(↑hu.unit⁻¹:l5)•P
  have hm:Q.Monic:=Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu
  have hQ:Q.eval₂ g.toRingHom z=0:= by
    change E Q=0
    rw [show Q=z1z (↑hu.unit⁻¹:l5)*P by
      simp [Q,Polynomial.smul_eq_C_mul],map_mul,hP,mul_zero]
  refine @eaT l5 (nW ⧸ J) _ _ g.toRingHom z Q hm hQ ?_
  intro y
  obtain ⟨x,hx⟩:=hE y
  exact ⟨x,hx⟩
theorem proof :Pw.c5:= by
  classical
  intro A _ _ _ d L hd hdu hspan hL
  let _:Infinite dF :=
    Infinite.of_injective _ (zxb (zM1 aR.ao) dF)
  obtain ⟨p,n,hp,hrel,hrest⟩:=c79 d hd (dOS d L hL)
  obtain ⟨t,ht⟩:=bXf hp hrest
  let w:=d 1-algebraMap dF A t*d 2
  have hw:IsUnit (zVv (zye {d 0}) w) :=
    gsH d hspan t hp hrel ht
  have hmap :adv d (aWh t)=biw (d 0) w:= by
    apply zpH
    intro i
    fin_cases i
    · simp [adv,ab4,aWh,aj1]
    · simp [adv,ab4,aWh,aj1,w,
        zpj,sub_mul,mul_assoc]
  exact ⟨aWh t,w,eaP d t hp hrel ht,hmap,
    hmap.symm ▸ eLm (F:=dF) (d 0) w hd hdu hw,hw⟩
end
end bzv
end
section
namespace cx4
noncomputable section
open Algebra aR B7 Ey Pw aFR
open scoped TensorProduct nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
private theorem aFj (k B:Type) [zrb k] [za6 B] [ztn B]
  [zZE k B] :trdeg k (FractionRing B)=trdeg k B:= by
 let:zjH B (FractionRing B) :=
  (zE4 (K:=FractionRing B)).mpr inferInstance
 rw [← trdeg_add_eq k B,trdeg_eq_zero (R:=B),add_zero]
private theorem ct7 {k B:Type} [zrb k] [za6 B] [ztn B]
  [zZE k B] {n:ℕ} (u:z3y (Fin n) k →ₐ[k] B)
  (hu:zq4 u) (hfin:u.Finite) :trdeg k B=n:= by
 let P:=z3y (Fin n) k
 let:zZE P B:=u.toRingHom.toAlgebra
 let:zsf k P B:=zKB u
 let:FaithfulSMul P B:=(faithfulSMul_iff_algebraMap_injective P B).mpr hu
 let:zAa P B:=hfin
 rw [← trdeg_add_eq k P (A:=B),trdeg_eq_zero (R:=P),add_zero,
  zUx,Cardinal.lift_id,Cardinal.mk_fin]
private theorem gxL {k σ:Type} [zrb k] [Finite σ]
   (I:znc (z3y σ k)) [ztn (z3y σ k ⧸ I)]
   (h: (zIU I).natDegree=2) :
   trdeg k (FractionRing (z3y σ k ⧸ I))=2 := by
 obtain ⟨n,u,hu,hfin⟩:=exists_finite_inj_algHom_of_fg k (z3y σ k ⧸ I)
 have hn:n=2 := by
   simpa only [MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective
     u hfin hu,zJa] using h
 rw [aFj,ct7 u hu hfin,hn]
 rfl
private theorem gEe (k :Type) [zrb k] :
  trdeg k (FractionRing (z3y (Fin 2) k))=2 := by
 rw [aFj]
 simp
private def localizedEquiv {P K A E :Type} [za6 P] [zrb K] [za6 A] [zrb E]
   [zZE P K] [z0o P K] [zZE P A] [zZE A E] [z0o A E]
   [zZE K E] [zjH K E]
   (h : ∀ p,algebraMap K E (algebraMap P K p)=algebraMap A E (algebraMap P A p)) :
   K ⊗[P] A ≃ₗ[K] E := by
 letI:zZE P E :=((algebraMap A E).comp (algebraMap P A)).toAlgebra
 letI:zsf P K E :=zsL fun p=>(h p).symm
 let T:=K ⊗[P] A
 let j:A →ₐ[P] E :=⟨algebraMap A E,fun _=>rfl⟩
 let f :T →ₐ[K] E :=zuh P K A E j
 letI:zZE A T:=Algebra.TensorProduct.rightAlgebra
 let S:=Algebra.algebraMapSubmonoid A (nonZeroDivisors P)
 letI:IsLocalization S T:=IsLocalization.tensorRight K (nonZeroDivisors P)
 have hf (a :A) :f (algebraMap A T a)=algebraMap A E a := by
   change (zuh P K A E j) (1 ⊗ₜ[P] a)= _
   rw [AlgHom.liftEquiv_tmul,one_smul]
   rfl
 have hinj:zq4 f := by
   apply (IsLocalization.injective_iff_map_algebraMap_eq S f.toRingHom).mpr
   intro x y
   constructor
   · exact congrArg f
   · intro hxy
     change f (algebraMap A T x)=f (algebraMap A T y) at hxy
     rw [hf,hf] at hxy
     exact congrArg (algebraMap A T) (zxb A E hxy)
 have hsurj:zpX f := by
   intro z
   obtain ⟨u,v,_,rfl⟩:=zJC A z
   change algebraMap A E u/algebraMap A E v∈f.range
   have hu:algebraMap A E u∈f.range :=⟨algebraMap A T u,hf u⟩
   have hv :algebraMap A E v∈f.range :=⟨algebraMap A T v,hf v⟩
   have hi: (algebraMap A E v)⁻¹∈f.range :=
     f.range.inv_mem_of_algebraic (x :=⟨_,hv⟩) (Algebra.IsAlgebraic.isAlgebraic _)
   simpa only [div_eq_mul_inv] using f.range.mul_mem hu hi
 exact (AlgEquiv.ofBijective f ⟨hinj,hsurj⟩).toLinearEquiv
private abbrev fiber {k P:Type} [za6 k] [za6 P] [zZE k P]
   (K:Type) [zrb K] [zZE P K] {A:Type} [za6 A] [zZE k A]
   (φ:P →ₐ[k] A) :Type :=
 letI:zeq P A:=zki A φ.toRingHom
 K ⊗[P] A
private def fiberEquiv {k P K A:Type} [zrb k] [za6 P] [zrb K] [zZE k P]
  [zZE P K] [z0o P K] [za6 A] [ztn A] [zZE k A]
  (φ:P →ₐ[k] A) [zZE K (FractionRing A)] [zjH K (FractionRing A)]
  (h : ∀ p,algebraMap K (FractionRing A) (algebraMap P K p)=asz A (φ p)) :
  fiber K φ ≃ₗ[K] FractionRing A:= by
 letI:zZE P A:=φ.toRingHom.toAlgebra
 exact localizedEquiv h
private theorem cRN {k P K A:Type} [zrb k] [za6 P] [zrb K] [zZE k P]
    [zZE P K] [z0o P K] [za6 A] [zZE k A]
    (φ:P →ₐ[k] A) {p:P} (hp:p≠0) (hz :φ p=0) :
    zAa K (fiber K φ)∧zsE K (fiber K φ)=0:= by
  let:zeq P A:=zki A φ.toRingHom
  have hp' : algebraMap P K p≠0 :=
    by simpa only [map_zero] using (zxb P K).ne hp
  have hzero (z :fiber K φ) :z=0:= by
    induction z using z2P with
    | tmul x a =>
      have heq :p•(x/algebraMap P K p)=x := by
        rw [zd5,mul_comm,div_mul_cancel₀ _ hp']
      calc
        x ⊗ₜ[P] a=(p•(x/algebraMap P K p)) ⊗ₜ[P] a := by
          rw [heq]
        _=(x/algebraMap P K p) ⊗ₜ[P] (p•a) :=
          TensorProduct.smul_tmul _ _ _
        _=0:= by
          change _ ⊗ₜ[P] (φ p*a)= _
          rw [hz,zero_mul,TensorProduct.tmul_zero]
    | add x y hx hy=>rw [hx,hy,zero_add]
  let:zOt (fiber K φ) :=⟨fun x y=>(hzero x).trans (hzero y).symm⟩
  exact ⟨inferInstance,zuF⟩
private theorem eaK {k K E :Type} [zrb k] [zrb K] [zrb E]
  [zZE k K] [zZE k E] [zl5 k E] (i:K →ₐ[k] E)
  (hK:trdeg k K=2) (hE :trdeg k E=2) :
  letI:zZE K E :=i.toRingHom.toAlgebra
  zjH K E∧zAa K E := by
 let:zZE K E :=i.toRingHom.toAlgebra
 let:zsf k K E :=zKB i
 have h:=trdeg_add_eq k K (A:=E)
 rw [hK,hE,add_comm 2] at h
 have halg:zjH K E := by
  apply trdeg_eq_zero_iff.mp
  apply (Cardinal.add_right_inj_of_lt_aleph0 (γ:=2) (by simp)).mp
  rw [h,zero_add]
 let:zl5 K E :=z9q k K E
 exact ⟨halg,zNf⟩
private def bKd {k P K A:Type} [zrb k] [za6 P] [zrb K]
  [zZE k P] [zZE P K] [z0o P K] [zZE k K] [zsf k P K]
  [za6 A] [ztn A] [zZE k A]
  {φ:P →ₐ[k] A} (hφ:zq4 φ) :K →ₐ[k] FractionRing A :=
 zeU
  (g:=(zE2 k A (FractionRing A)).comp φ)
  ((zxb A (FractionRing A)).comp hφ)
private theorem c3q {k P K A:Type} [zrb k] [za6 P] [zrb K]
  [zZE k P] [zZE P K] [z0o P K] [zZE k K] [zsf k P K]
  [za6 A] [ztn A] [zZE k A] {φ:P →ₐ[k] A}
  (hφ:zq4 φ) (p:P) :
  bKd (K:=K) hφ (algebraMap P K p)=asz A (φ p) := by
 unfold bKd
 rw [IsFractionRing.liftAlgHom_apply,zoc]
 rfl
private theorem dOn {k P K B A:Type} [zrb k] [za6 P] [zrb K]
   [zZE k P] [zZE P K] [z0o P K] [zZE k K] [zsf k P K]
   [za6 B] [ztn B] [zZE k B] [Algebra.FiniteType k B]
   [za6 A] [ztn A] [zZE k A]
   (φ:P →ₐ[k] B) (ψ:P →ₐ[k] A) (e :FractionRing B ≃ₐ[k] FractionRing A)
   (hK:trdeg k K=2) (hB:trdeg k (FractionRing B)=2)
   (he : ∀ p,e (asz B (φ p))=asz A (ψ p)) :
   zAa K (fiber K ψ)∧zsE K (fiber K ψ)=zsE K (fiber K φ) := by
 by_cases hφ:zq4 φ
 · have hψ:zq4 ψ:= by
     intro x y hxy
     apply hφ
     apply zxb B (FractionRing B)
     apply e.injective
     rw [he x,he y,hxy]
   let:zl5 B (FractionRing B) :=
     zrU _ (nonZeroDivisors B)
   let:zl5 k (FractionRing B) :=
     zQi k B (FractionRing B)
   let i:K →ₐ[k] FractionRing B:=bKd hφ
   let j:K →ₐ[k] FractionRing A:=bKd hψ
   obtain ⟨halg,hfinite⟩:=eaK i hK hB
   let:zZE K (FractionRing B) :=i.toRingHom.toAlgebra
   let:zZE K (FractionRing A) :=j.toRingHom.toAlgebra
   let:zjH K (FractionRing B) :=halg
   let:zAa K (FractionRing B) :=hfinite
   have hi (p:P) :i (algebraMap P K p)=asz B (φ p) :=c3q hφ p
   have hj (p:P) :j (algebraMap P K p)=asz A (ψ p) :=c3q hψ p
   have he' : e.toRingHom.comp i.toRingHom=j.toRingHom:= by
     apply z2O (A:=P)
     intro p
     change e (i (algebraMap P K p))=j (algebraMap P K p)
     rw [hi,hj,he]
   let e' : FractionRing B ≃ₐ[K] FractionRing A :=
     AlgEquiv.ofRingEquiv (f :=e.toRingEquiv) fun x=>zLs he' x
   let:zjH K (FractionRing A) :=e'.isAlgebraic
   let l:=fiberEquiv φ hi
   let r :=fiberEquiv ψ hj
   let fiberComparison :=(l.trans e'.toLinearEquiv).trans r.symm
   let:zAa K (fiber K φ) :=zZc l.symm
   exact ⟨zZc fiberComparison,fiberComparison.finrank_eq.symm⟩
 · obtain ⟨x,y,hxy,hne⟩:=Function.not_injective_iff.mp hφ
   have hp:x - y≠0:=sub_ne_zero.mpr hne
   have hz :φ (x - y)=0:= by rw [map_sub,hxy,sub_self]
   have hz' : ψ (x - y)=0:= by
     apply zxb A (FractionRing A)
     rw [← he (x - y),hz,map_zero,map_zero,map_zero]
   obtain ⟨_,hl⟩:=cRN (K:=K) φ hp hz
   obtain ⟨hr,hrank⟩:=cRN (K:=K) ψ hp hz'
   exact ⟨hr,hrank.trans hl.symm⟩
section zI
variable {k σ:Type} [zrb k] [Finite σ]
local notation "cAc" => MvPolynomial (Fin 2) k
local notation "a0U" => FractionRing (MvPolynomial (Fin 2) k)
private theorem dOo
  (I:znc (z3y σ k)) [ztn (z3y σ k ⧸ I)]
  (A:Type) [za6 A] [ztn A] [zZE k A]
  (φ:cAc →ₐ[k] (z3y σ k ⧸ I)) (ψ:cAc →ₐ[k] A)
  (e :FractionRing (z3y σ k ⧸ I) ≃ₐ[k] FractionRing A)
  (hdim: (zIU I).natDegree=2)
  (he : ∀ p,e (asz (z3y σ k ⧸ I) (φ p))=asz A (ψ p)) :
  zAa a0U (fiber a0U ψ) ∧
    zsE a0U (fiber a0U ψ)=zsE a0U (fiber a0U φ) :=
 dOn (K:=a0U) φ ψ e (gEe k) (gxL I hdim) he
end zI
theorem proof :aFR.c2 :=
 dOo (k :=dF) (σ:=rS)
end
end cx4
end
section
namespace cx2
noncomputable section
open aR Pw
open Polynomial
open scoped Polynomial
@[ext] private structure Jet (R:Type) where
  value :R
  first:R
  second:R
private def aom {R:Type} [za6 R] (x y :Jet R) :Jet R :=
 ⟨x.value*y.value,
   x.first*y.value + x.value*y.first,
   x.second*y.value+2*x.first*y.first + x.value*y.second⟩
private instance {R:Type} [za6 R] :CommMonoid (Jet R) where
 one :=⟨1,0,0⟩
 mul :=aom
 one_mul x := by
  change aom ⟨1,0,0⟩ x=x
  apply Jet.ext <;> simp [aom]
 mul_one x := by
  change aom x ⟨1,0,0⟩=x
  apply Jet.ext <;> simp [aom]
 mul_assoc x y z := by
  change aom (aom x y) z=aom x (aom y z)
  apply Jet.ext <;> simp only [aom] <;> ring
 mul_comm x y := by
  change aom x y=aom y x
  apply Jet.ext <;> simp only [aom] <;> ring
private def a7x {A:Type} [za6 A] :A[X] →* Jet A[X] where
  toFun g:=⟨g,derivative g,derivative (derivative g)⟩
  map_one' := by
    change (⟨1,derivative 1,derivative (derivative 1)⟩:Jet A[X])=⟨1,0,0⟩
    simp
  map_mul' g h:= by
    apply Jet.ext
    · rfl
    · exact derivative_mul
    · change derivative (derivative (g*h)) =
        derivative (derivative g)*h+2*derivative g*derivative h +
          g*derivative (derivative h)
      simp only [derivative_mul,map_add]
      ring
private def awj {R:Type} [za6 R] :R →* Jet R where
 toFun a :=⟨a,0,0⟩
 map_one' := rfl
 map_mul' a b:= by
  change ⟨a*b,0,0⟩=aom ⟨a,0,0⟩ ⟨b,0,0⟩
  simp [aom]
private def djn {R:Type} [za6 R] :Jet R →* R where
 toFun:=Jet.value
 map_one' := rfl
 map_mul' _ _:=rfl
private def aEx {A:Type} [za6 A] (g:A[X]) :ℕ→Jet A[X]
  | 0=>1
  | 1=>a7x g
  | k+2 =>
    ⟨g^2,
      C ((k+2 :ℕ) :A)*g*derivative g,
      C ((k+2 :ℕ) :A)*C ((k+1 :ℕ) :A)*derivative g^2 +
        C ((k+2 :ℕ) :A)*g*derivative (derivative g)⟩
private theorem c7E {A:Type} [za6 A] (g:A[X]) (m:ℕ) :
   (aEx g m).value=g^min m 2 := by
 match m with
 | 0=>exact (pow_zero g).symm
 | 1=>exact (pow_one g).symm
 | k+2 =>
   change g^2=g^min (k+2) 2
   rw [min_eq_right (by omega)]
private theorem fTR {A:Type} [za6 A] (g:A[X]) (m:ℕ) :
    a7x (g^m)=awj (g^(m - 2))*aEx g m:= by
  match m with
  | 0=>simp [aEx]
  | 1=>simp [aEx]
  | k+2 =>
    apply Jet.ext
    · change g^(k+2)=g^k*g^2
      exact pow_add g k 2
    · change derivative (g^(k+2)) =
        0*g^2+g^k*(C ((k+2 :ℕ) :A)*g*derivative g)
      rw [zero_mul,zero_add,derivative_pow_succ,pow_succ g k]
      simp only [z6H,z4o,Nat.cast_ofNat,map_add,map_one,map_ofNat]
      ring
    · change derivative (derivative (g^(k+2))) =
        0*g^2+2*0*(C ((k+2 :ℕ) :A)*g*derivative g) +
          g^k*(C ((k+2 :ℕ) :A)*C ((k+1 :ℕ) :A)*derivative g^2 +
            C ((k+2 :ℕ) :A)*g*derivative (derivative g))
      rw [derivative_pow_succ,derivative_mul,derivative_C_mul,
        derivative_pow_succ,pow_succ g k]
      simp only [z6H,z4o,Nat.cast_ofNat,map_add,map_one,map_ofNat]
      ring
private def aWT {A:Type} [za6 A] {f :A[X]}
   (s :Factorization f) :Jet A[X] :=
 ∏ i,aEx (s.factor i) (s.multiplicity i)
private theorem c7F {A:Type} [za6 A] {f :A[X]}
  (s :Factorization f) : (aWT s).value=aFm s := by
 change djn (∏ i,aEx (s.factor i) (s.multiplicity i))= _
 rw [map_prod,aFm]
 exact zX3 rfl (fun i _=>c7E _ _)
private theorem fTQ {A:Type} [za6 A] {f :A[X]}
    (s :Factorization f) :
    a7x f=awj (auF s)*aWT s := by
  calc
    a7x f = ∏ i,a7x (s.factor i^s.multiplicity i) :=
      (congrArg a7x s.product_eq).trans (map_prod a7x _ _)
    _ = ∏ i,awj (s.factor i^(s.multiplicity i - 2)) *
        aEx (s.factor i) (s.multiplicity i) :=
      zX3 rfl (fun i _=>fTR _ _)
    _ = _:= by rw [zeY,auF,map_prod,aWT]
private theorem cTQ {n:ℕ} (hpos :0<n) (hsmall:n<K1.p) :
  (n:ao)≠0:= by
 let _:CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
 intro h
 exact (not_le_of_gt hsmall) (Nat.le_of_dvd hpos
  ((CharP.cast_eq_zero_iff ao K1.p n).mp h))
private theorem cVF {A:Type} [za6 A] [zZE ao A]
  {n:ℕ} (hpos :0<n) (hsmall:n≤133671) :IsUnit (C (n:A)) := by
 let ι:ao →+* A[X] :=C.comp (algebraMap ao A)
 have hu:=(isUnit_iff_ne_zero.mpr (cTQ hpos
  (hsmall.trans_lt (by decide :133671<K1.p)))).map ι
 simpa only [ι,zQb,map_natCast] using hu
private theorem c1N {R:Type} [za6 R] {P:znc R}
  (hP:P ≠ ⊤) {x y :R} (hx :x∈P) (hxy :IsCoprime x y) :y∉P:= by
 intro hy
 obtain ⟨a,b,hab⟩:=hxy
 exact hP ((zhc P).mpr (hab ▸ P.add_mem (P.mul_mem_left a hx)
  (P.mul_mem_left b hy)))
private theorem fVg {A:Type} [za6 A] [zZE ao A]
    {f :A[X]} (s :Factorization f) (P:znc A[X]) [hP:P.IsPrime]
    (hv : (aWT s).value∈P) :
    (aWT s).first∉P∨(aWT s).second∉P:= by
  classical
  rw [c7F,aFm] at hv
  obtain ⟨i,hi,hiPow⟩:=Ideal.IsPrime.prod_mem_iff.mp hv
  have hgi:=hP.mem_of_pow_mem _ hiPow
  let g:=s.factor i
  let m:=s.multiplicity i
  have hm:0< m∧m≤133671 :=s.multiplicity_bounds i
  have hd:derivative g∉P :=
    c1N hP.ne_top' hgi (s.derivative_coprime i)
  let t := ∏ j∈Finset.univ.erase i,aEx (s.factor j) (s.multiplicity j)
  have ht:t.value∉P:= by
    change djn (∏ j∈Finset.univ.erase i,
      aEx (s.factor j) (s.multiplicity j))∉P
    rw [map_prod]
    intro h
    obtain ⟨j,hj,hjPow⟩:=Ideal.IsPrime.prod_mem_iff.mp h
    change (aEx (s.factor j) (s.multiplicity j)).value∈P at hjPow
    rw [c7E] at hjPow
    exact (c1N hP.ne_top' hgi
      (s.pairwise_coprime (Finset.ne_of_mem_erase hj).symm)) (hP.mem_of_pow_mem _ hjPow)
  have he :aWT s=aEx g m*t :=
    (Finset.mul_prod_erase _ _ hi).symm
  have hg:g∈P:=hgi
  by_cases hm1 :m=1
  · left
    rw [he,hm1]
    change derivative g*t.value+g*t.first∉P
    intro h
    exact hP.mul_notMem hd ht (by simpa using P.sub_mem h (P.mul_mem_right t.first hg))
  · right
    have hm2 :m=(m - 2)+2 := by omega
    let k :=m - 2
    have hk :m=k+2 :=hm2
    have hu0:C ((k+2 :ℕ) :A)∉P :=
      P.notMem_of_isUnit (cVF (by omega :0<k+2) (by omega :k+2≤133671))
    have hu1 :C ((k+1 :ℕ) :A)∉P :=
      P.notMem_of_isUnit (cVF (by omega :0<k+1) (by omega :k+1≤133671))
    rw [he,hk]
    let a :A[X] :=C ((k+2 :ℕ) :A)
    let b:A[X] :=C ((k+1 :ℕ) :A)
    change (a*b*derivative g^2+a*g*derivative (derivative g))*t.value +
      2*(a*g*derivative g)*t.first+g^2*t.second∉P
    intro h
    have h₁:a*g*derivative (derivative g)*t.value∈P :=
      P.mul_mem_right _ (P.mul_mem_right _ (P.mul_mem_left _ hg))
    have h₂:2*(a*g*derivative g)*t.first∈P :=
      P.mul_mem_right _ (P.mul_mem_left _ (P.mul_mem_right _ (P.mul_mem_left _ hg)))
    have h₃:g^2*t.second∈P:=P.mul_mem_right _ (P.pow_mem_of_mem hg 2 (by decide))
    rw [add_mul] at h
    have h' := P.sub_mem (P.sub_mem (P.sub_mem h h₃) h₂) h₁
    have hn:a*b*derivative g^2*t.value∉P :=
      hP.mul_notMem (hP.mul_notMem (hP.mul_notMem hu0 hu1)
        (fun h=>hd (hP.mem_of_pow_mem 2 h))) ht
    exact hn (by simpa using h')
private def half (A:Type) [za6 A] [zZE ao A] :A[X] :=
 C (algebraMap ao A ((2 :ao)⁻¹))
private theorem diy (A:Type) [za6 A] [zZE ao A] :
  (2 :A[X])*half A=1 := by
 let ι:ao →+* A[X] :=C.comp (algebraMap ao A)
 have htwo:=cTQ (n:=2) (by decide) (by decide)
 have hh: (2 :ao)*(2 :ao)⁻¹=1 :=mul_inv_cancel₀ htwo
 change (2 :A[X])*ι ((2 :ao)⁻¹)=1
 simpa only [map_mul,map_ofNat,map_one] using congrArg ι hh
private theorem gEW {A:Type} [za6 A] (f :A[X]) :
  (2 :A[X])*hasseDeriv 2 f=derivative (derivative f) := by
 simpa [Nat.factorial,nsmul_eq_mul,Function.iterate_succ_apply'] using
  congrFun (factorial_smul_hasseDeriv (R:=A) 2) f
theorem proof :Pw.c3:= by
  intro A _ _ f s
  let t:=aWT s
  let q:Fin 3→ A[X] := ![t.value,t.first,half A*t.second]
  have he :=fTQ s
  have h0:f=auF s*t.value :=congrArg Jet.value he
  have h1 :derivative f=auF s*t.first:= by
    have h:=congrArg Jet.first he
    change derivative f=0*t.value+auF s*t.first at h
    simpa only [zero_mul,zero_add] using h
  have h2 :derivative (derivative f)=auF s*t.second:= by
    have h:=congrArg Jet.second he
    change derivative (derivative f) =
      0*t.value+2*0*t.first+auF s*t.second at h
    simpa only [mul_zero,zero_mul,zero_add] using h
  refine ⟨q,c7F s,?_,?_⟩
  · intro j
    fin_cases j
    · simpa [q] using h0.symm
    · simpa [q] using h1.symm
    · change auF s*(half A*t.second)=hasseDeriv 2 f
      calc
        auF s*(half A*t.second) =
            half A*(auF s*t.second) := by ac_rfl
        _=half A*derivative (derivative f) := by rw [h2]
        _ = _:= by rw [← gEW,← mul_assoc,mul_comm (half A),diy,one_mul]
  · by_contra h
    obtain ⟨P,hP,hle⟩:=zsl _ h
    let _:P.IsPrime :=hP.isPrime
    have hmem (j:Fin 3) :q j∈P:=hle (zCn ⟨j,rfl⟩)
    have hsecond:t.second∈P:= by
      have hh:half A*t.second∈P:=hmem 2
      have hh' := P.mul_mem_left (2 :A[X]) hh
      rwa [← mul_assoc,diy,one_mul] at hh'
    exact (fVg s P (hmem 0)).elim
      (fun hfirst=>hfirst (hmem 1)) (fun hn=>hn hsecond)
end
end cx2
end
section
namespace cxZ
open MvPolynomial
theorem proof :ap5.c2 := by
 intro F σ _ _ I ℓ hI _ hℓ hregular
 have hcolon :I.colon {ℓ} = I:= by
   refine le_antisymm ?_ Ideal.le_colon
   intro a ha
   have hmul :ℓ*a∈I:= by
     rw [mul_comm]
     simpa only [Submodule.mem_colon_singleton,smul_eq_mul] using ha
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   apply hregular
   change zVv I ℓ* zVv I a=zVv I ℓ*0
   rw [mul_zero,← map_mul]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr hmul
 have h:=aeD.b5W hI hℓ
 rw [hcolon,z4o] at h
 exact eq_sub_of_add_eq h
end cxZ
end
section
namespace fP
open aR Ex MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
private theorem bFD
  (x y :ao) (u v :JetVariable 3 →₀ ℕ) (a :ao)
  (hv :v∈(globalPointTranslation x y (monomial u a)).support) :v≤u:= by
 intro j
 let w:JetVariable 3→ℕ:=Pi.single j 1
 have h:monomial u a∈restrictWeightAtMost w (u j) := by
  rw [monomial_mem_restrictWeightAtMost]
  exact Or.inl (by simp [w,z7P])
 have hh:=globalPointTranslation_mem_restrictWeightAtMost (zD0 _) (zD0 _) x y h
 simpa only [w,z7P] using mem_restrictWeightAtMost.mp hh v hv
end
end fP
end
section
namespace aBb
noncomputable section
open cu gT
abbrev aLP (J:znc aZ) :=
 gk (J.map (zDK (algebraMap FX aQ)) ⊔
  zye {B4 0 1})
end
end aBb
end
